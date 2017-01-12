#include "idris_heap.h"
#include "idris_rts.h"
#include "idris_gc.h"
#include "idris_bitstring.h"
#include <assert.h>

VAL copy(VM* vm, VAL x) {
    int ar;
    Closure* cl = NULL;
    if (x==NULL || ISINT(x)) {
        return x;
    }
    switch(GETTY(x)) {
    case CT_CON:
        ar = CARITY(x);
        if (ar == 0 && CTAG(x) < 256) {
            return x;
        } else {
            allocCon(cl, vm, CTAG(x), ar, 1);
            memcpy(&(cl->info.c.args), &(x->info.c.args), sizeof(VAL)*ar);
        }
        break;
    case CT_FLOAT:
        cl = MKFLOATc(vm, x->info.f);
        break;
    case CT_STRING:
        cl = MKSTRc(vm, x->info.str);
        break;
    case CT_STROFFSET:
        cl = MKSTROFFc(vm, x->info.str_offset);
        break;
    case CT_BIGINT:
        cl = MKBIGMc(vm, x->info.ptr);
        break;
    case CT_PTR:
        cl = MKPTRc(vm, x->info.ptr);
        break;
    case CT_MANAGEDPTR:
        cl = MKMPTRc(vm, x->info.mptr->data, x->info.mptr->size);
        break;
    case CT_BITS8:
        cl = idris_b8CopyForGC(vm, x);
        break;
    case CT_BITS16:
        cl = idris_b16CopyForGC(vm, x);
        break;
    case CT_BITS32:
        cl = idris_b32CopyForGC(vm, x);
        break;
    case CT_BITS64:
        cl = idris_b64CopyForGC(vm, x);
        break;
    case CT_FWD:
        return x->info.ptr;
    case CT_RAWDATA:
        {
            size_t size = x->info.size + sizeof(Closure);
            cl = allocate(size, 0);
            memcpy(cl, x, size);
        }
        break;
    case CT_CDATA:
        cl = MKCDATAc(vm, x->info.c_heap_item);
        c_heap_mark_item(x->info.c_heap_item);
        break;
    default:
        break;
    }
    SETTY(x, CT_FWD);
    x->info.ptr = cl;
    return cl;
}

void cheney(VM *vm) {
    int i;
    int ar;
    char* scan = aligned_heap_pointer(vm->heap.heap);

    while(scan < vm->heap.next) {
       size_t inc = *((size_t*)scan);
       VAL heap_item = (VAL)(scan+sizeof(size_t));
       // If it's a CT_CON or CT_STROFFSET, copy its arguments
       switch(GETTY(heap_item)) {
       case CT_CON:
           ar = ARITY(heap_item);
           for(i = 0; i < ar; ++i) {
               VAL newptr = copy(vm, heap_item->info.c.args[i]);
               heap_item->info.c.args[i] = newptr;
           }
           break;
       case CT_STROFFSET:
           heap_item->info.str_offset->str
               = copy(vm, heap_item->info.str_offset->str);
           break;
       default: // Nothing to copy
           break;
       }
       scan += inc;
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
