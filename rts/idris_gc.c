#include "idris_rts.h"
#include "idris_gc.h"
#include <assert.h>

VAL copy(VM* vm, VAL x) {
    int i;
    VAL* argptr;
    Closure* cl = NULL;
    if (x==NULL || ISINT(x)) {
        return x;
    }
    switch(GETTY(x)) {
    case CON:
        cl = allocCon(vm, x->info.c.arity);
        cl->info.c.tag = x->info.c.tag;
        cl->info.c.arity = x->info.c.arity;

        argptr = (VAL*)(cl->info.c.args);
        for(i = 0; i < x->info.c.arity; ++i) {
//            *argptr = copy(vm, *((VAL*)(x->info.c.args)+i)); // recursive version
            *argptr = *((VAL*)(x->info.c.args)+i);
            argptr++;
        }
        break;
    case FLOAT:
        cl = MKFLOAT(vm, x->info.f);
        break;
    case STRING:
        cl = MKSTR(vm, x->info.str);
        break;
    case BIGINT:
        cl = MKBIGM(vm, x->info.ptr);
        break;
    case PTR:
        cl = MKPTR(vm, x->info.ptr);
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
    VAL* argptr;
    int i;
    char* scan = vm->heap;
  
    while(scan < vm->heap_next) {
       size_t inc = *((size_t*)scan);
       VAL heap_item = (VAL)(scan+sizeof(size_t));
       // If it's a CON, copy its arguments
       switch(GETTY(heap_item)) {
       case CON:
           argptr = (VAL*)(heap_item->info.c.args);
           for(i = 0; i < heap_item->info.c.arity; ++i) {
               // printf("Copying %d %p\n", heap_item->info.c.tag, *argptr);
               VAL newptr = copy(vm, *argptr);
               // printf("Got %p\t\t%p %p\n", newptr, scan, vm->heap_next);
               *argptr = newptr;
               argptr++;
           }
           break;
       default: // Nothing to copy
           break;
       }
       scan += inc;
    }
    assert(scan == vm->heap_next);
}

void gc(VM* vm) {
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

void gcInfo(VM* vm, int doGC) {
    printf("\nStack: %p %p\n", vm->valstack, vm->valstack_top); 
    printf("Total allocations: %d\n", vm->allocations);
    printf("GCs: %d\n", vm->collections);
    printf("Final heap size %d\n", (int)(vm->heap_size));
    printf("Final heap use %d\n", (int)(vm->heap_next - vm->heap));
    if (doGC) { gc(vm); }
    printf("Final heap use after GC %d\n", (int)(vm->heap_next - vm->heap));
}
