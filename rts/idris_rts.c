#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdarg.h>

#include "idris_rts.h"
#include "idris_gc.h"

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
    vm -> oldheap = NULL;
    vm -> heap_next = vm -> heap;
    vm -> heap_end = vm -> heap + heap_size;
    vm -> heap_size = heap_size;
    vm -> collections = 0;
    vm -> allocations = 0;
    vm -> heap_growth = heap_size;
    vm -> ret = NULL;
    return vm;
}

void* allocate(VM* vm, size_t size) {
    if ((size & 7)!=0) {
	size = 8 + ((size >> 3) << 3);
    }
    vm->allocations += size+sizeof(size_t)*2;
    if (vm -> heap_next + size < vm -> heap_end) {
        void* ptr = (void*)(((size_t*)(vm->heap_next))+2);
        *((size_t*)(vm->heap_next)) = size+sizeof(size_t)*2;
        vm -> heap_next += size+sizeof(size_t)*2;
        return ptr;
    } else {
        gc(vm);
        return allocate(vm, size);
    }
}

void* allocCon(VM* vm, int arity) {
    Closure* cl = allocate(vm, sizeof(Closure) + sizeof(VAL)*arity);
    cl -> ty = CON;
    if (arity == 0) {
       cl -> info.c.args = NULL;
    } else {
       cl -> info.c.args = (void*)((char*)cl + sizeof(Closure));
    }
    return (void*)cl;
}

VAL MKFLOAT(VM* vm, double val) {
    Closure* cl = allocate(vm, sizeof(Closure));
    cl -> ty = FLOAT;
    cl -> info.f = val;
    return cl;
}

VAL MKSTR(VM* vm, char* str) {
    Closure* cl = allocate(vm, sizeof(Closure) + // Type) + sizeof(char*) +
                               sizeof(char)*strlen(str)+1);
    cl -> ty = STRING;
    cl -> info.str = (char*)cl + sizeof(Closure);

    strcpy(cl -> info.str, str);
    return cl;
}

VAL MKPTR(VM* vm, void* ptr) {
    Closure* cl = allocate(vm, sizeof(Closure));
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
    Closure* cl = allocate(vm, sizeof(Closure) + sizeof(char)*16);
    cl -> ty = STRING;
    cl -> info.str = (char*)cl + sizeof(Closure);
    sprintf(cl -> info.str, "%ld", GETINT(i));
    return cl;
}

VAL idris_castStrInt(VM* vm, VAL i) {
    char *end;
    i_int v = strtol(GETSTR(i), &end, 10);
    if (*end != '\0') return MKINT(0); else return MKINT(v);
}

VAL idris_castFloatStr(VM* vm, VAL i) {
    Closure* cl = allocate(vm, sizeof(Closure) + sizeof(char)*32);
    cl -> ty = STRING;
    cl -> info.str = (char*)cl + sizeof(Closure);
    sprintf(cl -> info.str, "%g", GETFLOAT(i));
    return cl;
}

VAL idris_castStrFloat(VM* vm, VAL i) {
    return MKFLOAT(vm, strtod(GETSTR(i), NULL));
}

VAL idris_concat(VM* vm, VAL l, VAL r) {
    char *ls = GETSTR(l);
    char *rs = GETSTR(r);
    Closure* cl = allocate(vm, sizeof(Closure) + strlen(ls) + strlen(rs) + 1);
    // Oops! problem if the second allocate triggers a gc because cl has
    // to be a root. Fix by allocating all in one go.

    // Also note that l/r may be in from space, so don't delete after collection,
    // rather, delete just before the next collection.
    cl -> ty = STRING;
    cl -> info.str = (char*)cl + sizeof(Closure);
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

#define BUFSIZE 256

VAL idris_readStr(VM* vm, FILE* h) {
// Modified from 'safe-fgets.c' in the gdb distribution.
// (see http://www.gnu.org/software/gdb/current/)
    char *line_ptr;
    char* line_buf = (char *) malloc (BUFSIZE);
    int line_buf_size = BUFSIZE;

    /* points to last byte */
    line_ptr = line_buf + line_buf_size - 1;

    /* so we can see if fgets put a 0 there */
    *line_ptr = 1;
    if (fgets (line_buf, line_buf_size, h) == 0)
        return MKSTR(vm, "");

    /* we filled the buffer? */
    while (line_ptr[0] == 0 && line_ptr[-1] != '\n')
    {
        /* Make the buffer bigger and read more of the line */
        line_buf_size += BUFSIZE;
        line_buf = (char *) realloc (line_buf, line_buf_size);

        /* points to last byte again */
        line_ptr = line_buf + line_buf_size - 1;
        /* so we can see if fgets put a 0 there */
        *line_ptr = 1;

        if (fgets (line_buf + line_buf_size - BUFSIZE - 1, BUFSIZE + 1, h) == 0)
           return MKSTR(vm, "");
    }

    VAL str = MKSTR(vm, line_buf);
    free(line_buf);
    return str;
}


void stackOverflow() {
  fprintf(stderr, "Stack overflow");
  exit(-1);
}

