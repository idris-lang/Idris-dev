#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include "closure.h"

VM* init_vm(int stack_size, size_t heap_size) {
    VAL* valstack = malloc(stack_size*sizeof(VAL));
    int* intstack = malloc(stack_size*sizeof(int));
    double* floatstack = malloc(stack_size*sizeof(double));

    VM* vm = malloc(sizeof(VM));
    vm -> valstack = valstack;
    vm -> valstack_ptr = valstack;
    vm -> intstack = intstack;
    vm -> intstack_ptr = intstack;
    vm -> floatstack = floatstack;
    vm -> floatstack_ptr = floatstack;
    vm -> stack_max = stack_size;
    vm -> heap = malloc(heap_size);
    vm -> ret = NULL;
    return vm;
}

void* allocate(VM* vm, int size) {
    return malloc(size); // TMP!
}

void* allocThunk(VM* vm, int argspace) {
    Closure* cl = allocate(vm, sizeof(ClosureType) + 
                               sizeof(VAL) * (argspace + 1) +
                               sizeof(int) * 2);
    cl -> ty = THUNK;
    return (void*)cl;
}

void* allocCon(VM* vm, int arity) {
    Closure* cl = allocate(vm, sizeof(ClosureType) +
                               sizeof(int) +
                               sizeof(VAL) * arity);
    cl -> ty = CON;
    return (void*)cl;
}

VAL mkInt(VM* vm, int val) {
    Closure* cl = allocate(vm, sizeof(ClosureType) + sizeof(int));
    cl -> ty = INT;
    cl -> info.i = val;
    return cl;
}

VAL mkFloat(VM* vm, double val) {
    Closure* cl = allocate(vm, sizeof(ClosureType) + sizeof(double));
    cl -> ty = FLOAT;
    cl -> info.f = val;
    return cl;
}

VAL mkStr(VM* vm, char* str) {
    Closure* cl = allocate(vm, sizeof(ClosureType) + sizeof(char*) * strlen(str));
    cl -> ty = STRING;
    strcpy(cl -> info.str, str);
    return cl;
}

VAL mkThunk(VM* vm, func fn, int args, int arity) {
    int i;
    Closure* cl = allocThunk(vm, arity);
    cl -> info.t.fn = fn;
    cl -> info.t.arity = arity;
    cl -> info.t.numargs = args;
    VAL** argptr = &(cl -> info.t.args);

    for (i = 0; i < args; ++i) {
       VAL* v = POP;
       *argptr++ = v;
    }
}

VAL mkCon(VM* vm, int tag, int arity) {
    Closure* cl = allocCon(vm, arity);

    int i;
    cl -> info.c.tag = tag;
    VAL** argptr = &(cl -> info.c.args);

    for (i = 0; i < arity; ++i) {
       VAL* v = POP;
       *argptr++ = v;
    }
}

// if 'update' is set, update the value at the top of the stack
// otherwise, replace it with a new value

void EVAL(int update) {
    
}

void stackOverflow() {
  fprintf(stderr, "Stack overflow");
  exit(-1);
}
