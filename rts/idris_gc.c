#include "idris_rts.h"
#include "idris_gc.h"
#include "idris_bitstring.h"
#include <assert.h>

VAL copy(VM* vm, VAL x) {
    int i, ar;
    Closure* cl = NULL;
    if (x==NULL || ISINT(x)) {
        return x;
    }
    switch(GETTY(x)) {
    case CON:
        ar = CARITY(x);
        allocCon(cl, vm, CTAG(x), ar, 1);
        for(i = 0; i < ar; ++i) {
//            *argptr = copy(vm, *((VAL*)(x->info.c.args)+i)); // recursive version
            cl->info.c.args[i] = x->info.c.args[i];
        }
        break;
    case FLOAT:
        cl = MKFLOATc(vm, x->info.f);
        break;
    case STRING:
        cl = MKSTRc(vm, x->info.str);
        break;
    case STROFFSET:
        cl = MKSTROFFc(vm, x->info.str_offset);
        break;
    case BUFFER:
        cl = MKBUFFERc(vm, x->info.buf);
        break;
    case BIGINT:
        cl = MKBIGMc(vm, x->info.ptr);
        break;
    case PTR:
        cl = MKPTRc(vm, x->info.ptr);
        break;
    case MANAGEDPTR:
        cl = MKMPTRc(vm, x->info.mptr->data, x->info.mptr->size);
        break;
    case BITS8:
        cl = idris_b8CopyForGC(vm, x);
        break;
    case BITS16:
        cl = idris_b16CopyForGC(vm, x);
        break;
    case BITS32:
        cl = idris_b32CopyForGC(vm, x);
        break;
    case BITS64:
        cl = idris_b64CopyForGC(vm, x);
        break;
    case FWD:
        return x->info.ptr;
    default:
        break;
    }
    SETTY(x, FWD);
    x->info.ptr = cl;
    return cl;
}

void cheney(VM *vm) {
    int i;
    int ar;
    char* scan = vm->heap.heap;
  
    while(scan < vm->heap.next) {
       size_t inc = *((size_t*)scan);
       VAL heap_item = (VAL)(scan+sizeof(size_t));
       // If it's a CON or STROFFSET, copy its arguments
       switch(GETTY(heap_item)) {
       case CON:
           ar = ARITY(heap_item);
           for(i = 0; i < ar; ++i) {
               // printf("Copying %d %p\n", heap_item->info.c.tag, *argptr);
               VAL newptr = copy(vm, heap_item->info.c.args[i]);
               // printf("Got %p\t\t%p %p\n", newptr, scan, vm->heap_next);
               heap_item->info.c.args[i] = newptr;
           }
           break;
       case STROFFSET:
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
    // printf("Collecting\n");

    char* newheap = malloc(vm->heap.size);
    char* oldheap = vm->heap.heap;
    if (vm->heap.old != NULL) 
        free(vm->heap.old);

    vm->heap.heap = newheap;
#ifdef FORCE_ALIGNMENT
    if (((i_int)(vm->heap.heap)&1) == 1) {
        vm->heap.next = newheap + 1;
    } else
#endif
    {
        vm->heap.next = newheap;
    }
    vm->heap.end  = newheap + vm->heap.size;

    VAL* root;

    for(root = vm->valstack; root < vm->valstack_top; ++root) {
        *root = copy(vm, *root);
    }

#ifdef HAS_PTHREAD
    for(root = vm->inbox_ptr; root < vm->inbox_write; ++root) {
        *root = copy(vm, *root);
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
    vm->heap.old = oldheap;
    
    STATS_LEAVE_GC(vm->stats, vm->heap.size, vm->heap.next - vm->heap.heap)
    HEAP_CHECK(vm)
}

void idris_gcInfo(VM* vm, int doGC) {
    printf("Stack: <BOT %p> <TOP %p>\n", vm->valstack, vm->valstack_top); 
    printf("Final heap size         %d\n", (int)(vm->heap.size));
    printf("Final heap use          %d\n", (int)(vm->heap.next - vm->heap.heap));
    if (doGC) { idris_gc(vm); }
    printf("Final heap use after GC %d\n", (int)(vm->heap.next - vm->heap.heap));
}
