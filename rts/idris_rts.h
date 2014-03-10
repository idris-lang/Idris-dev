#ifndef _IDRISRTS_H
#define _IDRISRTS_H

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdarg.h>
#ifdef HAS_PTHREAD
#include <pthread.h>
#endif
#include <stdint.h>

#include "idris_heap.h"
#include "idris_stats.h"

// Closures

typedef enum {
    CON, INT, BIGINT, FLOAT, STRING, STROFFSET,
    BITS8, BITS16, BITS32, BITS64, UNIT, PTR, FWD,
    MANAGEDPTR, BUFFER
} ClosureType;

typedef struct Closure *VAL;

typedef struct {
    int tag_arity;
    VAL args[];
} con;

typedef struct {
    VAL str;
    int offset;
} StrOffset;

typedef struct {
    // If we ever have multithreaded access to the same heap,
    // fill is mutable so needs synchronization!
    size_t fill;
    size_t cap;
    unsigned char store[];
} Buffer;

// A foreign pointer, managed by the idris GC
typedef struct {
    size_t size;
    void* data;
} ManagedPtr;

typedef struct Closure {
// Use top 16 bits of ty for saying which heap value is in
// Bottom 16 bits for closure type
    ClosureType ty;
    union {
        con c;
        int i;
        double f;
        char* str;
        StrOffset* str_offset;
        void* ptr;
        uint8_t bits8;
        uint16_t bits16;
        uint32_t bits32;
        uint64_t bits64;
        Buffer* buf;
        ManagedPtr* mptr;
    } info;
} Closure;

typedef struct {
    VAL* valstack;
    VAL* valstack_top;
    VAL* valstack_base;
    VAL* stack_max;
    
    Heap heap;
#ifdef HAS_PTHREAD
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
#endif
    Stats stats;

    VAL ret;
    VAL reg1;
} VM;

// Create a new VM
VM* init_vm(int stack_size, size_t heap_size, 
            int max_threads);
// Clean up a VM once it's no longer needed
Stats terminate(VM* vm);

// Functions all take a pointer to their VM, and previous stack base, 
// and return nothing.
typedef void(*func)(VM*, VAL*);

// Register access 

#define RVAL (vm->ret)
#define LOC(x) (*(vm->valstack_base + (x)))
#define TOP(x) (*(vm->valstack_top + (x)))
// Doesn't work! Ordinary assign seems fine though...
#define UPDATE(x,y) if (!ISINT(x) && !ISINT(y)) \
   { (x)->ty = (y)->ty; (x)->info = (y)->info; }
#define REG1 (vm->reg1)

// Retrieving values

#define GETSTR(x) (ISSTR(x) ? (((VAL)(x))->info.str) : GETSTROFF(x))
#define GETPTR(x) (((VAL)(x))->info.ptr) 
#define GETMPTR(x) (((VAL)(x))->info.mptr->data) 
#define GETFLOAT(x) (((VAL)(x))->info.f)

#define TAG(x) (ISINT(x) || x == NULL ? (-1) : ( (x)->ty == CON ? (x)->info.c.tag_arity >> 8 : (-1)) )
#define ARITY(x) (ISINT(x) || x == NULL ? (-1) : ( (x)->ty == CON ? (x)->info.c.tag_arity & 0x000000ff : (-1)) )

// Already checked it's a CON
#define CTAG(x) (((x)->info.c.tag_arity) >> 8)
#define CARITY(x) ((x)->info.c.tag_arity & 0x000000ff)

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
#define ISSTR(x) (((VAL)(x))->ty == STRING)

#define INTOP(op,x,y) MKINT((i_int)((((i_int)x)>>1) op (((i_int)y)>>1)))
#define UINTOP(op,x,y) MKINT((i_int)((((uintptr_t)x)>>1) op (((uintptr_t)y)>>1)))
#define FLOATOP(op,x,y) MKFLOAT(vm, ((GETFLOAT(x)) op (GETFLOAT(y))))
#define FLOATBOP(op,x,y) MKINT((i_int)(((GETFLOAT(x)) op (GETFLOAT(y)))))
#define ADD(x,y) (void*)(((i_int)x)+(((i_int)y)-1))
#define MULT(x,y) (MKINT((((i_int)x)>>1) * (((i_int)y)>>1)))

// Stack management

#define INITFRAME VAL* myoldbase
#define REBASE vm->valstack_base = oldbase
#define RESERVE(x) if (vm->valstack_top+(x) > vm->stack_max) { stackOverflow(); } \
                   else { memset(vm->valstack_top, 0, (x)*sizeof(VAL)); }
#define ADDTOP(x) vm->valstack_top += (x)
#define TOPBASE(x) vm->valstack_top = vm->valstack_base + (x)
#define BASETOP(x) vm->valstack_base = vm->valstack_top + (x)
#define STOREOLD myoldbase = vm->valstack_base
#define CALL(f) f(vm, myoldbase);
#define TAILCALL(f) f(vm, oldbase);

// Creating new values (each value placed at the top of the stack)
VAL MKFLOAT(VM* vm, double val);
VAL MKSTR(VM* vm, const char* str);
VAL MKPTR(VM* vm, void* ptr);
VAL MKMPTR(VM* vm, void* ptr, int size);
VAL MKB8(VM* vm, uint8_t b);
VAL MKB16(VM* vm, uint16_t b);
VAL MKB32(VM* vm, uint32_t b);
VAL MKB64(VM* vm, uint64_t b);

// following versions don't take a lock when allocating
VAL MKFLOATc(VM* vm, double val);
VAL MKSTROFFc(VM* vm, StrOffset* off);
VAL MKSTRc(VM* vm, char* str);
VAL MKPTRc(VM* vm, void* ptr);
VAL MKMPTRc(VM* vm, void* ptr, int size);
VAL MKBUFFERc(VM* vm, Buffer* buf);

char* GETSTROFF(VAL stroff);

// #define SETTAG(x, a) (x)->info.c.tag = (a)
#define SETARG(x, i, a) ((x)->info.c.args)[i] = ((VAL)(a))
#define GETARG(x, i) ((x)->info.c.args)[i]

void PROJECT(VM* vm, VAL r, int loc, int arity); 
void SLIDE(VM* vm, int args);

void* allocate(VM* vm, size_t size, int outerlock);
// void* allocCon(VM* vm, int arity, int outerlock);

// When allocating from C, call 'idris_requireAlloc' with a size to
// guarantee that no garbage collection will happen (and hence nothing
// will move) until at least size bytes have been allocated.
// idris_doneAlloc *must* be called when allocation from C is done (as it
// may take a lock if other threads are running).

void idris_requireAlloc(VM* vm, size_t size);
void idris_doneAlloc(VM* vm);

#define allocCon(cl, vm, t, a, o) \
  cl = allocate(vm, sizeof(Closure) + sizeof(VAL)*a, o); \
  SETTY(cl, CON); \
  cl->info.c.tag_arity = ((t) << 8) + (a);

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

// Raw memory manipulation
void idris_memset(void* ptr, i_int offset, uint8_t c, i_int size);
uint8_t idris_peek(void* ptr, i_int offset);
void idris_poke(void* ptr, i_int offset, uint8_t data);
void idris_memmove(void* dest, void* src, i_int dest_offset, i_int src_offset, i_int size);

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

// Buffer primitives
VAL idris_allocate(VM* vm, VAL hint);
VAL idris_appendBuffer(VM* vm, VAL fst, VAL fstLen, VAL cnt, VAL sndLen, VAL sndOff, VAL snd);
VAL idris_appendB8Native(VM* vm, VAL buf, VAL len, VAL cnt, VAL val);
VAL idris_appendB16Native(VM* vm, VAL buf, VAL len, VAL cnt, VAL val);
VAL idris_appendB16LE(VM* vm, VAL buf, VAL len, VAL cnt, VAL val);
VAL idris_appendB16BE(VM* vm, VAL buf, VAL len, VAL cnt, VAL val);
VAL idris_appendB32Native(VM* vm, VAL buf, VAL len, VAL cnt, VAL val);
VAL idris_appendB32LE(VM* vm, VAL buf, VAL len, VAL cnt, VAL val);
VAL idris_appendB32BE(VM* vm, VAL buf, VAL len, VAL cnt, VAL val);
VAL idris_appendB64Native(VM* vm, VAL buf, VAL len, VAL cnt, VAL val);
VAL idris_appendB64LE(VM* vm, VAL buf, VAL len, VAL cnt, VAL val);
VAL idris_appendB64BE(VM* vm, VAL buf, VAL len, VAL cnt, VAL val);
VAL idris_peekB8Native(VM* vm, VAL buf, VAL off);
VAL idris_peekB16Native(VM* vm, VAL buf, VAL off);
VAL idris_peekB16LE(VM* vm, VAL buf, VAL off);
VAL idris_peekB16BE(VM* vm, VAL buf, VAL off);
VAL idris_peekB32Native(VM* vm, VAL buf, VAL off);
VAL idris_peekB32LE(VM* vm, VAL buf, VAL off);
VAL idris_peekB32BE(VM* vm, VAL buf, VAL off);
VAL idris_peekB64Native(VM* vm, VAL buf, VAL off);
VAL idris_peekB64LE(VM* vm, VAL buf, VAL off);
VAL idris_peekB64BE(VM* vm, VAL buf, VAL off);

// Command line args

extern int __idris_argc;
extern char **__idris_argv;

int idris_numArgs();
const char *idris_getArg(int i);

// Handle stack overflow. 
// Just reports an error and exits.

void stackOverflow();

// Some FFI help (functions and macros below are all which C code should
// use)

// When allocating from C, call 'idris_requireAlloc' with a size to
// guarantee that no garbage collection will happen (and hence nothing
// will move) until at least size bytes have been allocated.
// idris_doneAlloc *must* be called when allocation from C is done (as it
// may take a lock if other threads are running).

void idris_requireAlloc(VM* vm, size_t size);
void idris_doneAlloc(VM* vm);

// I think these names are nicer for an API...

#define idris_constructor allocCon
#define idris_setConArg SETARG
#define idris_getConArg GETARG
#define idris_mkInt(x) MKINT((intptr_t)(x))

#include "idris_gmp.h"

#endif 
