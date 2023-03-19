#include "idris_heap.h"
#include "idris_rts.h"
#include "idris_gc.h"
#include "idris_bitstring.h"
#ifndef BARE_METAL
#include <assert.h>
#else
#include "idris_bare_metal.h"
#endif

static inline VAL copy_plain(VM* vm, VAL x, size_t sz) {
    VAL cl = iallocate(vm, sz, 1);
    memcpy(cl, x, sz);
    return cl;
}

VAL copy(VM* vm, VAL x) {
    int ar;
    VAL cl;
    if (x==NULL) {
        return x;
    }
    switch(GETTY(x)) {
    case CT_INT: return x;
    case CT_BITS32: return copy_plain(vm, x, sizeof(Bits32));
    case CT_BITS64: return copy_plain(vm, x, sizeof(Bits64));
    case CT_FLOAT: return copy_plain(vm, x, sizeof(Float));
    case CT_FWD:
        return GETPTR(x);
    case CT_CDATA:
        cl = copy_plain(vm, x, sizeof(CDataC));
        c_heap_mark_item(GETCDATA(x));
        break;
    case CT_BIGINT:
        cl = MKBIGMc(vm, GETMPZ(x));
        break;
    case CT_CON:
        ar = CARITY(x);
        if (ar == 0 && CTAG(x) < 256) {
            return x;
        }
        // FALLTHROUGH
    case CT_ARRAY:
    case CT_STRING:
    case CT_REF:
    case CT_STROFFSET:
    case CT_PTR:
    case CT_MANAGEDPTR:
    case CT_RAWDATA:
        cl = copy_plain(vm, x, x->hdr.sz);
        break;
    default:
        cl = NULL;
        assert(0);
        break;
    }
    assert(x->hdr.sz >= sizeof(Fwd));
    SETTY(x, CT_FWD);
    ((Fwd*)x)->fwd = cl;
    return cl;
}

void cheney(VM *vm) {
    char* scan = aligned_heap_pointer(vm->heap.heap);

    while(scan < vm->heap.next) {
       VAL heap_item = (VAL)scan;
       // If it's a CT_CON, CT_REF or CT_STROFFSET, copy its arguments
       switch(GETTY(heap_item)) {
       case CT_CON:
           {
               Con * c = (Con*)heap_item;
               size_t len = CARITY(c);
               for(size_t i = 0; i < len; ++i)
                   c->args[i] = copy(vm, c->args[i]);
           }
           break;
       case CT_ARRAY:
           {
               Array * a = (Array*)heap_item;
               size_t len = CELEM(a);
               for(size_t i = 0; i < len; ++i)
                   a->array[i] = copy(vm, a->array[i]);
           }
           break;
       case CT_REF:
           {
               Ref * r = (Ref*)heap_item;
               r->ref = copy(vm, r->ref);
           }
           break;
       case CT_STROFFSET:
           {
               StrOffset * s = (StrOffset*)heap_item;
               s->base = (String*)copy(vm, (VAL)s->base);
           }
           break;
       default: // Nothing to copy
           break;
       }
       scan += aligned(valSize(heap_item));
    }
    assert(scan == vm->heap.next);
}

void idris_gc(VM* vm) {
    HEAP_CHECK(vm)
    STATS_ENTER_GC(vm->stats, vm->heap.size)

    if (vm->heap.old != NULL)
        free(vm->heap.old);

    /* Allocate swap heap. */
    alloc_heap(&vm->heap, vm->heap.size, vm->heap.growth, vm->heap.heap);

    VAL* root;

    for(root = vm->valstack; root < vm->valstack_top; ++root) {
        *root = copy(vm, *root);
    }

#ifdef HAS_PTHREAD
    Msg* msg;

    for(msg = vm->inbox; msg < vm->inbox_write; ++msg) {
        msg->msg = copy(vm, msg->msg);
    }
#endif

    vm->ret = copy(vm, vm->ret);
    vm->reg1 = copy(vm, vm->reg1);

    cheney(vm);

    // After reallocation, if we've still more than half filled the new heap, grow the heap
    // for next time.

    if ((vm->heap.next - vm->heap.heap) > vm->heap.size >> 1) {
        vm->heap.size += vm->heap.growth;
    }

    // finally, sweep the C heap
    c_heap_sweep(&vm->c_heap);

    STATS_LEAVE_GC(vm->stats, vm->heap.size, vm->heap.next - vm->heap.heap)
    HEAP_CHECK(vm)
}

void idris_gcInfo(VM* vm, int doGC) {
    printf("Stack: <BOT %p> <TOP %p>\n", vm->valstack, vm->valstack_top);
    printf("Final heap size         %zd\n", vm->heap.size);
    printf("Final heap use          %zd\n", vm->heap.next - vm->heap.heap);
    if (doGC) { idris_gc(vm); }
    printf("Final heap use after GC %zd\n", vm->heap.next - vm->heap.heap);
#ifdef IDRIS_ENABLE_STATS
    printf("Total allocations       %" PRIu64 "\n", vm->stats.allocations);
#endif
    printf("Number of collections   %" PRIu32 "\n", vm->stats.collections);

}
