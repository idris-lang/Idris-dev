#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdarg.h>

#include "closure.h"

VM* init_vm(int stack_size, size_t heap_size) {
    VAL* valstack = malloc(stack_size*sizeof(VAL));
    int* intstack = malloc(stack_size*sizeof(int));
    double* floatstack = malloc(stack_size*sizeof(double));

    VM* vm = malloc(sizeof(VM));
    vm -> valstack = valstack;
    vm -> valstack_top = valstack;
    vm -> valstack_base = valstack;
    vm -> intstack = intstack;
    vm -> intstack_ptr = intstack;
    vm -> floatstack = floatstack;
    vm -> floatstack_ptr = floatstack;
    vm -> stack_max = stack_size;
    vm -> heap = malloc(heap_size);
    vm -> heap_next = vm -> heap;
    vm -> ret = NULL;
    return vm;
}

void* allocate(VM* vm, int size) {
    return malloc(size); // TMP!
}

void* allocCon(VM* vm, int arity) {
    Closure* cl = allocate(vm, sizeof(ClosureType) +
                               sizeof(con));
    cl -> ty = CON;
    if (arity == 0) {
       cl -> info.c.args = NULL;
    } else {
       cl -> info.c.args = allocate(vm, sizeof(VAL)*arity);
    }
    return (void*)cl;
}

VAL MKFLOAT(VM* vm, double val) {
    Closure* cl = allocate(vm, sizeof(ClosureType) + sizeof(double));
    cl -> ty = FLOAT;
    cl -> info.f = val;
    return cl;
}

VAL MKSTR(VM* vm, char* str) {
    Closure* cl = allocate(vm, sizeof(ClosureType) + sizeof(char*));
    cl -> ty = STRING;
    cl -> info.str = allocate(vm, sizeof(char)*strlen(str)+1);
    strcpy(cl -> info.str, str);
    return cl;
}

VAL MKCON(VM* vm, int tag, int arity, ...) {
    Closure* cl;
    int i;
    va_list args;

    va_start(args, arity);

    cl = allocCon(vm, arity);
    cl -> info.c.tag = tag;
    cl -> info.c.arity = arity;
    VAL* argptr = (VAL*)(cl -> info.c.args);

    for (i = 0; i < arity; ++i) {
       VAL v = va_arg(args, VAL);
       *argptr = v;
       argptr++;
    }
    va_end(args);

    return cl;
}

void PROJECT(VM* vm, VAL r, int loc, int arity) {
    int i;
    VAL* argptr = (VAL*)(r -> info.c.args);
    
    for(i = 0; i < arity; ++i) {
        LOC(i+loc) = *argptr++;
    }
}

void dumpVal(VAL v) {
    int i;
    switch(v->ty) {
    case CON:
        printf("%d[", v->info.c.tag);
        for(i = 0; i < v->info.c.arity; ++i) {
            VAL* args = (VAL*)v->info.c.args;
            dumpVal(args[i]);
        }
        printf("] ");
    }

}

void stackOverflow() {
  fprintf(stderr, "Stack overflow");
  exit(-1);
}

