#include "idris_rts.h"
#include "idris_gc.h"

VAL copy(VM* vm, VAL x) {
    int i;
    VAL* argptr;
    Closure* cl;
    if (x==NULL || ISINT(x)) {
        return x;
    }
    switch(x->ty) {
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
    case PTR:
        cl = MKPTR(vm, x->info.ptr);
        break;
    case FWD:
        cl = x->info.ptr;
        break;
    }
    x->ty = FWD;
    x->info.ptr = cl;
    return cl;
}

void cheney(VM *vm) {
    VAL* argptr;
    int i;
    char* scan = vm->heap;
   
    while(scan < vm->heap_next) {
       size_t inc = *((size_t*)scan);
       VAL heap_item = (VAL)(scan+sizeof(size_t)*2);
       // If it's a CON, copy its arguments
       switch(heap_item->ty) {
       case CON:
           argptr = (VAL*)(heap_item->info.c.args);
           for(i = 0; i < heap_item->info.c.arity; ++i) {
               *argptr = copy(vm, *argptr);
               argptr++;
           }
           break;
       }
       scan += inc;
    }
}

void gc(VM* vm) {
    char* newheap = malloc(vm -> heap_size);
    char* oldheap = vm -> heap;

    vm->heap = newheap;
    vm->heap_next = newheap;
    vm->heap_end = newheap + vm->heap_size;

    vm->collections++;

    VAL* root;

    for(root = vm->valstack; root < vm->valstack_top; ++root) {
        *root = copy(vm, *root);
    }
    vm->ret = copy(vm, vm->ret);
    cheney(vm);

    // After reallocation, if we've still more than half filled the new heap, grow the heap
    // for next time.

    if ((vm->heap_next - vm->heap) > vm->heap_size >> 1) {
        vm->heap_size += vm->heap_growth;
    }

    free(oldheap);
}
