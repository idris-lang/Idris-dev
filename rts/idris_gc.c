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
    case BIGINT:
        cl = MKBIGMc(vm, x->info.ptr);
        break;
    case PTR:
        cl = MKPTRc(vm, x->info.ptr);
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
    char* scan = vm->heap;
  
    while(scan < vm->heap_next) {
       size_t inc = *((size_t*)scan);
       VAL heap_item = (VAL)(scan+sizeof(size_t));
       // If it's a CON, copy its arguments
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
       default: // Nothing to copy
           break;
       }
       scan += inc;
    }
    assert(scan == vm->heap_next);
}

void idris_gc(VM* vm) {
    // printf("Collecting\n");

    char* newheap = malloc(vm -> heap_size);
    char* oldheap = vm -> heap;
    if (vm->oldheap != NULL) free(vm->oldheap);

    vm->heap = newheap;
    vm->heap_next = newheap;
    vm->heap_end = newheap + vm->heap_size;

    vm->collections++;

    VAL* root;

    for(root = vm->valstack; root < vm->valstack_top; ++root) {
        *root = copy(vm, *root);
    }
    for(root = vm->inbox_ptr; root < vm->inbox_write; ++root) {
        *root = copy(vm, *root);
    }
    for(root = vm->argv; root < vm->argv + vm->argc; ++root) {
        *root = copy(vm, *root);
    }
    vm->ret = copy(vm, vm->ret);
    vm->reg1 = copy(vm, vm->reg1);

    cheney(vm);

    // After reallocation, if we've still more than half filled the new heap, grow the heap
    // for next time.

    if ((vm->heap_next - vm->heap) > vm->heap_size >> 1) {
        vm->heap_size += vm->heap_growth;
    } 
    vm->oldheap = oldheap;
    
    // gcInfo(vm, 0);
}

void idris_gcInfo(VM* vm, int doGC) {
    printf("\nStack: %p %p\n", vm->valstack, vm->valstack_top); 
    printf("Total allocations: %d\n", vm->allocations);
    printf("GCs: %d\n", vm->collections);
    printf("Final heap size %d\n", (int)(vm->heap_size));
    printf("Final heap use %d\n", (int)(vm->heap_next - vm->heap));
    if (doGC) { idris_gc(vm); }
    printf("Final heap use after GC %d\n", (int)(vm->heap_next - vm->heap));
}
