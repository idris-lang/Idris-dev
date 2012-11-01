#ifndef _IDRISRTS_H
#define _IDRISRTS_H

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdarg.h>
#include <pthread.h>

// Closures

typedef enum {
    CON, INT, BIGINT, FLOAT, STRING, UNIT, PTR, FWD
} ClosureType;

typedef struct Closure *VAL;

typedef struct {
    int tag;
    int arity;
    VAL args[];
} con;

typedef struct Closure {
// Use top 16 bits of ty for saying which heap value is in
// Bottom 16 bits for closure type
    ClosureType ty;
    union {
        con c;
        int i;
        double f;
        char* str;
        void* ptr;
    } info;
} Closure;

typedef struct {
    VAL* valstack;
    int* intstack;
    double* floatstack;
    VAL* valstack_top;
    VAL* valstack_base;
    int* intstack_ptr;
    double* floatstack_ptr;
    char* heap;
    char* oldheap;
    char* heap_next;
    char* heap_end;
    VAL* stack_max;
   
    pthread_mutex_t inbox_lock;
    pthread_mutex_t inbox_block;
    pthread_mutex_t alloc_lock;
    pthread_cond_t inbox_waiting;

    VAL* inbox; // Block of memory for storing messages
    VAL* inbox_end; // End of block of memory

    VAL* inbox_ptr; // Next message to read
    VAL* inbox_write; // Location of next message to write

    int processes; // Number of child processes
    int max_threads; // maximum number of threads to run in parallel

    int argc;
    VAL* argv; // command line arguments

    size_t heap_size;
    size_t heap_growth;
    int allocations;
    int collections;
    VAL ret;
    VAL reg1;
} VM;

// Create a new VM
VM* init_vm(int stack_size, size_t heap_size, 
            int max_threads, 
            int argc, char* argv[]);
// Clean up a VM once it's no longer needed
void terminate(VM* vm);

// Functions all take a pointer to their VM, and previous stack base, 
// and return nothing.
typedef void(*func)(VM*, VAL*);

// Register access 

#define RVAL (vm->ret)
#define LOC(x) (*(vm->valstack_base + (x)))
#define TOP(x) (*(vm->valstack_top + (x)))
#define REG1 (vm->reg1)

// Retrieving values

#define GETSTR(x) (((VAL)(x))->info.str) 
#define GETPTR(x) (((VAL)(x))->info.ptr) 
#define GETFLOAT(x) (((VAL)(x))->info.f)

#define TAG(x) (ISINT(x) || x == NULL ? (-1) : ( (x)->ty == CON ? (x)->info.c.tag : (-1)) )

// Use top 16 bits for saying which heap value is in
// Bottom 16 bits for closure type

#define GETTY(x) ((x)->ty & 0x0000ffff)
#define SETTY(x,t) (x)->ty = (((x)->ty & 0xffff0000) | (t))

#define GETHEAP(x) ((x)->ty >> 16)
#define SETHEAP(x,y) (x)->ty = (((x)->ty & 0x0000ffff) | ((t) << 16))

// Integers, floats and operators

typedef intptr_t i_int;

#define MKINT(x) ((void*)((x)<<1)+1)
#define GETINT(x) ((i_int)(x)>>1)
#define ISINT(x) ((((i_int)x)&1) == 1)

#define INTOP(op,x,y) MKINT((i_int)((((i_int)x)>>1) op (((i_int)y)>>1)))
#define FLOATOP(op,x,y) MKFLOAT(vm, ((GETFLOAT(x)) op (GETFLOAT(y))))
#define FLOATBOP(op,x,y) MKINT((i_int)(((GETFLOAT(x)) op (GETFLOAT(y)))))
#define ADD(x,y) (void*)(((i_int)x)+(((i_int)y)-1))
#define MULT(x,y) (MKINT((((i_int)x)>>1) * (((i_int)y)>>1)))

// Stack management

#define INITFRAME VAL* myoldbase
#define REBASE vm->valstack_base = oldbase
#define RESERVE(x) if (vm->valstack_top+(x) > vm->stack_max) { stackOverflow(); } \
                   else { bzero(vm->valstack_top, (x)*sizeof(VAL)); }
#define ADDTOP(x) vm->valstack_top += (x)
#define TOPBASE(x) vm->valstack_top = vm->valstack_base + (x)
#define BASETOP(x) vm->valstack_base = vm->valstack_top + (x)
#define STOREOLD myoldbase = vm->valstack_base

#define CALL(f) f(vm, myoldbase);
#define TAILCALL(f) f(vm, oldbase);

// Creating new values (each value placed at the top of the stack)
VAL MKFLOAT(VM* vm, double val);
VAL MKSTR(VM* vm, char* str);
VAL MKPTR(VM* vm, void* ptr);

// following versions don't take a lock when allocating
VAL MKFLOATc(VM* vm, double val);
VAL MKSTRc(VM* vm, char* str);
VAL MKPTRc(VM* vm, void* ptr);

VAL MKCON(VM* vm, VAL cl, int tag, int arity, ...);

#define SETTAG(x, a) (x)->info.c.tag = (a)
#define SETARG(x, i, a) ((x)->info.c.args)[i] = ((VAL)(a))
#define GETARG(x, i) ((x)->info.c.args)[i]

void PROJECT(VM* vm, VAL r, int loc, int arity); 
void SLIDE(VM* vm, int args);

void* allocate(VM* vm, size_t size, int outerlock);
void* allocCon(VM* vm, int arity, int outerlock);

void* vmThread(VM* callvm, func f, VAL arg);

// Copy a structure to another vm's heap
VAL copyTo(VM* newVM, VAL x);

// Add a message to another VM's message queue
void idris_sendMessage(VM* sender, VM* dest, VAL msg);
// Check whether there are any messages in the queue
int idris_checkMessages(VM* vm);
// block until there is a message in the queue
VAL idris_recvMessage(VM* vm);

void dumpVal(VAL r);
void dumpStack(VM* vm);

// Casts

#define idris_castIntFloat(x) MKFLOAT(vm, (double)(GETINT(x)))
#define idris_castFloatInt(x) MKINT((i_int)(GETFLOAT(x)))

VAL idris_castIntStr(VM* vm, VAL i);
VAL idris_castStrInt(VM* vm, VAL i);
VAL idris_castFloatStr(VM* vm, VAL i);
VAL idris_castStrFloat(VM* vm, VAL i);

// String primitives

VAL idris_concat(VM* vm, VAL l, VAL r);
VAL idris_strlt(VM* vm, VAL l, VAL r);
VAL idris_streq(VM* vm, VAL l, VAL r);
VAL idris_strlen(VM* vm, VAL l);
VAL idris_readStr(VM* vm, FILE* h);

VAL idris_strHead(VM* vm, VAL str);
VAL idris_strTail(VM* vm, VAL str);
VAL idris_strCons(VM* vm, VAL x, VAL xs);
VAL idris_strIndex(VM* vm, VAL str, VAL i);
VAL idris_strRev(VM* vm, VAL str);

// Command line args

int idris_numArgs(VM* vm);
VAL idris_getArg(VM* vm, int i);

// Handle stack overflow. 
// Just reports an error and exits.

void stackOverflow();

#include "idris_gmp.h"

#endif 
