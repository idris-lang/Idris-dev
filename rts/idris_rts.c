#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdarg.h>

#include "idris_rts.h"

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

VAL MKPTR(VM* vm, void* ptr) {
    Closure* cl = allocate(vm, sizeof(ClosureType) + sizeof(void*));
    cl -> ty = PTR;
    cl -> info.ptr = ptr;
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

void SLIDE(VM* vm, int args) {
    int i;
    for(i = 0; i < args; ++i) {
        LOC(i) = TOP(i);
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

VAL idris_castIntStr(VM* vm, VAL i) {
    Closure* cl = allocate(vm, sizeof(ClosureType) + sizeof(char*));
    cl -> ty = STRING;
    cl -> info.str = allocate(vm, sizeof(char)*16);
    sprintf(cl -> info.str, "%ld", GETINT(i));
    return cl;
}

VAL idris_castStrInt(VM* vm, VAL i) {
    char *end;
    i_int v = strtol(GETSTR(i), &end, 10);
    if (*end != '\0') return MKINT(0); else return MKINT(v);
}

VAL idris_castFloatStr(VM* vm, VAL i) {
    Closure* cl = allocate(vm, sizeof(ClosureType) + sizeof(char*));
    cl -> ty = STRING;
    cl -> info.str = allocate(vm, sizeof(char)*32);
    sprintf(cl -> info.str, "%g", GETFLOAT(i));
    return cl;
}

VAL idris_castStrFloat(VM* vm, VAL i) {
    return MKFLOAT(vm, strtod(GETSTR(i), NULL));
}

VAL idris_concat(VM* vm, VAL l, VAL r) {
    char *ls = GETSTR(l);
    char *rs = GETSTR(r);

    Closure* cl = allocate(vm, sizeof(ClosureType) + sizeof(char*));
    cl -> ty = STRING;
    cl -> info.str = allocate(vm, sizeof(char)*(strlen(ls)+strlen(rs)+1));
    strcpy(cl -> info.str, ls);
    strcat(cl -> info.str, rs); 
    return cl;
}

VAL idris_strlt(VM* vm, VAL l, VAL r) {
    char *ls = GETSTR(l);
    char *rs = GETSTR(r);

    return MKINT((i_int)(strcmp(ls, rs) < 0));
}

VAL idris_streq(VM* vm, VAL l, VAL r) {
    char *ls = GETSTR(l);
    char *rs = GETSTR(r);

    return MKINT((i_int)(strcmp(ls, rs) == 0));
}

VAL idris_strlen(VM* vm, VAL l) {
    return MKINT((i_int)(strlen(GETSTR(l))));
}

VAL idris_readStr(VM* vm, FILE* h) {
}


void stackOverflow() {
  fprintf(stderr, "Stack overflow");
  exit(-1);
}

