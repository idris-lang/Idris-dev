#ifndef _IDRISRTS_H
#define _IDRISRTS_H

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#ifdef HAS_PTHREAD
#include <string.h>
#include <stdarg.h>
#include <pthread.h>
#endif

#include "idris_heap.h"
#include "idris_stats.h"


#ifndef EXIT_SUCCESS
#define EXIT_SUCCESS 0
#endif
#ifndef EXIT_FAILURE
#define EXIT_FAILURE 1
#endif

// Closures
typedef enum {
    CT_CON, CT_ARRAY, CT_INT, CT_BIGINT,
    CT_FLOAT, CT_STRING, CT_STROFFSET, CT_BITS8,
    CT_BITS16, CT_BITS32, CT_BITS64, CT_PTR,
    CT_REF, CT_FWD, CT_MANAGEDPTR, CT_RAWDATA,
    CT_CDATA
} ClosureType;

typedef struct Hdr {
    uint8_t ty;
    uint8_t u8;
    uint16_t u16;
    uint32_t sz;
} Hdr;

typedef struct Val {
    Hdr hdr;
} Val;

typedef struct Val * VAL;

typedef struct Con {
    Hdr hdr;
    uint32_t tag;
    VAL args[0];
} Con;

typedef struct Array {
    Hdr hdr;
    VAL array[0];
} Array;

typedef struct Int {
    Hdr hdr;
    int i;
} Int;

typedef struct BigInt {
    Hdr hdr;
    char big[0];
} BigInt;

typedef struct Float {
    Hdr hdr;
    double f;
} Float;

typedef struct String {
    Hdr hdr;
    size_t slen;
    char str[0];
} String;

typedef struct StrOffset {
    Hdr hdr;
    String * base;
    size_t offset;
} StrOffset;

typedef struct Bits8 {
    Hdr hdr;
    uint8_t bits8;
} Bits8;

typedef struct Bits16 {
    Hdr hdr;
    uint16_t bits16;
} Bits16;

typedef struct Bits32 {
    Hdr hdr;
    uint32_t bits32;
} Bits32;

typedef struct Bits64 {
    Hdr hdr;
    uint64_t bits64;
} Bits64;

typedef struct Ptr {
    Hdr hdr;
    void * ptr;
} Ptr;

typedef struct Ref {
    Hdr hdr;
    VAL ref;
} Ref;

typedef struct Fwd {
    Hdr hdr;
    VAL fwd;
} Fwd;

typedef struct ManagedPtr {
    Hdr hdr;
    char mptr[0];
} ManagedPtr;

typedef struct RawData {
    Hdr hdr;
    char raw[0];
} RawData;

typedef struct CDataC {
    Hdr hdr;
    CHeapItem * item;
} CDataC;

struct VM;

struct Msg_t {
    struct VM* sender;
    // An identifier to say which conversation this message is part of.
    // Lowest bit is set if the id is the first message in a conversation.
    int channel_id;
    VAL msg;
};

typedef struct Msg_t Msg;

struct VM {
    int active; // 0 if no longer running; keep for message passing
                // TODO: If we're going to have lots of concurrent threads,
                // we really need to be cleverer than this!

    VAL* valstack;
    VAL* valstack_top;
    VAL* valstack_base;
    VAL* stack_max;

    CHeap c_heap;
    Heap heap;
#ifdef HAS_PTHREAD
    pthread_mutex_t inbox_lock;
    pthread_mutex_t inbox_block;
    pthread_mutex_t alloc_lock;
    pthread_cond_t inbox_waiting;

    Msg* inbox; // Block of memory for storing messages
    Msg* inbox_end; // End of block of memory
    int inbox_nextid; // Next channel id
    Msg* inbox_write; // Location of next message to write

    int processes; // Number of child processes
    int max_threads; // maximum number of threads to run in parallel
#endif
    Stats stats;

    VAL ret;
    VAL reg1;
};

typedef struct VM VM;


/* C data interface: allocation on the C heap.
 *
 * Although not enforced in code, CData is meant to be opaque
 * and non-RTS code (such as libraries or C bindings) should
 * access only its (void *) field called "data".
 *
 * Feel free to mutate cd->data; the heap does not care
 * about its particular value. However, keep in mind
 * that it must not break Idris's referential transparency.
 *
 * If you call cdata_allocate or cdata_manage, the resulting
 * CData object *must* be returned from your FFI function so
 * that it is inserted in the C heap. Otherwise the memory
 * will be leaked.
 */

/// C data block. Contains (void * data).
typedef CHeapItem * CData;

/// Allocate memory, returning the corresponding C data block.
CData cdata_allocate(size_t size, CDataFinalizer * finalizer);

/// Wrap a pointer as a C data block.
/// The size should be an estimate of how much memory, in bytes,
/// is associated with the pointer. This estimate need not be absolutely precise
/// but it is necessary for GC to work effectively.
CData cdata_manage(void * data, size_t size, CDataFinalizer * finalizer);


// Create a new VM
VM* init_vm(int stack_size, size_t heap_size,
            int max_threads);

// Get the VM for the current thread
VM* get_vm(void);
// Initialise thread-local data for this VM
void init_threaddata(VM *vm);
// Clean up a VM once it's no longer needed
Stats terminate(VM* vm);

// Create a new VM, set up everything with sensible defaults (use when
// calling Idris from C)
VM* idris_vm(void);
void close_vm(VM* vm);

// Set up key for thread-local data - called once from idris_main
void init_threadkeys(void);

// Functions all take a pointer to their VM, and previous stack base,
// and return nothing.
typedef void(*func)(VM*, VAL*);

// Register access

#define RVAL (vm->ret)
#define LOC(x) (vm->valstack_base[x])
#define TOP(x) (vm->valstack_top[x])
#define REG1 (vm->reg1)

// Retrieving values
static inline char * getstr(String * x) {
    // hdr.u8 used to mark a null string
    return x->hdr.u8? NULL : x->str;
}

static inline size_t getstrlen(String * x) {
    return x->slen;
}

#define GETSTR(x) (ISSTR(x) ? getstr((String*)(x)) : GETSTROFF(x))
#define GETSTRLEN(x) (ISSTR(x) ? getstrlen((String*)(x)) : GETSTROFFLEN(x))
#define GETPTR(x) (((Ptr*)(x))->ptr)
#define GETMPTR(x) (((ManagedPtr*)(x))->mptr)
#define GETFLOAT(x) (((Float*)(x))->f)
#define GETCDATA(x) (((CDataC*)(x))->item)

#define GETBITS8(x) (((Bits8*)(x))->bits8)
#define GETBITS16(x) (((Bits16*)(x))->bits16)
#define GETBITS32(x) (((Bits32*)(x))->bits32)
#define GETBITS64(x) (((Bits64*)(x))->bits64)

// Already checked it's a CT_CON
#define CTAG(x) (((Con*)(x))->tag)
#define CARITY(x) (((Con*)(x))->hdr.u16) // hdr.u16 used to store arity

#define TAG(x) (ISINT(x) || x == NULL ? (-1) : ( GETTY(x) == CT_CON ? CTAG((Con*)x) : (-1)) )
#define ARITY(x) (ISINT(x) || x == NULL ? (-1) : ( GETTY(x) == CT_CON ? CARITY((Con*)x) : (-1)) )

#define CELEM(x) (((x)->hdr.sz - sizeof(Array)) / sizeof(VAL))

#define GETTY(x) ((ClosureType)((x)->hdr.ty))
#define SETTY(x,t) ((x)->hdr.ty = t)

// Integers, floats and operators

typedef intptr_t i_int;

// Shifting a negative number left is undefined and (rightly) gives a warning,
// but we're only interested in shifting the bit pattern, so cast it
#define MKINT(x) ((void*)((i_int)((((uintptr_t)x)<<1)+1)))
#define GETINT(x) ((i_int)(x)>>1)
#define ISINT(x) ((((i_int)x)&1) == 1)
#define ISSTR(x) (GETTY(x) == CT_STRING)

#define INTOP(op,x,y) MKINT((i_int)((((i_int)x)>>1) op (((i_int)y)>>1)))
#define UINTOP(op,x,y) MKINT((i_int)((((uintptr_t)x)>>1) op (((uintptr_t)y)>>1)))
#define FLOATOP(op,x,y) MKFLOAT(vm, ((GETFLOAT(x)) op (GETFLOAT(y))))
#define FLOATBOP(op,x,y) MKINT((i_int)(((GETFLOAT(x)) op (GETFLOAT(y)))))
#define ADD(x,y) (void*)(((i_int)x)+(((i_int)y)-1))
#define MULT(x,y) (MKINT((((i_int)x)>>1) * (((i_int)y)>>1)))

// Stack management

#ifdef IDRIS_TRACE
#define TRACE idris_trace(vm, __FUNCTION__, __LINE__);
#else
#define TRACE
#endif

#define INITFRAME TRACE\
                  __attribute__((unused)) VAL* myoldbase

#define REBASE vm->valstack_base = oldbase
#define RESERVE(x) do { \
    if (vm->valstack_top+(x) > vm->stack_max) { stackOverflow(); } \
    else { memset(vm->valstack_top, 0, (x)*sizeof(VAL)); } \
  } while(0)
#define ADDTOP(x) vm->valstack_top += (x)
#define TOPBASE(x) vm->valstack_top = vm->valstack_base + (x)
#define BASETOP(x) vm->valstack_base = vm->valstack_top + (x)
#define STOREOLD myoldbase = vm->valstack_base
#define CALL(f) f(vm, myoldbase);
#define TAILCALL(f) f(vm, oldbase);

// Creating new values (each value placed at the top of the stack)
VAL MKFLOAT(VM* vm, double val);
VAL MKSTR(VM* vm, const char* str);
VAL MKSTRlen(VM* vm, const char* str, size_t size);
VAL MKPTR(VM* vm, void* ptr);
VAL MKMPTR(VM* vm, void* ptr, size_t size);
VAL MKB8(VM* vm, uint8_t b);
VAL MKB16(VM* vm, uint16_t b);
VAL MKB32(VM* vm, uint32_t b);
VAL MKB64(VM* vm, uint64_t b);
VAL MKCDATA(VM* vm, CHeapItem * item);

// following versions don't take a lock when allocating
VAL MKFLOATc(VM* vm, double val);
VAL MKSTROFFc(VM* vm, VAL basestr);
VAL MKSTRc(VM* vm, char* str);
VAL MKSTRclen(VM* vm, char* str, size_t len);
VAL MKPTRc(VM* vm, void* ptr);
VAL MKMPTRc(VM* vm, void* ptr, size_t size);
VAL MKCDATAc(VM* vm, CHeapItem * item);

char* GETSTROFF(VAL stroff);
size_t GETSTROFFLEN(VAL stroff);

#define SETARG(x, i, a) (((Con*)(x))->args)[i] = ((VAL)(a))
#define GETARG(x, i) (((Con*)(x))->args[i])

#define PROJECT(vm,r,loc,num) \
    memcpy(&(LOC(loc)), ((Con*)(r))->args, sizeof(VAL)*num)
#define SLIDE(vm, args) \
    memcpy(&(LOC(0)), &(TOP(0)), sizeof(VAL)*args)

void* iallocate(VM *, size_t, int);

void* allocate(size_t size, int outerlock);
// void* allocCon(VM* vm, int arity, int outerlock);

// When allocating from C, call 'idris_requireAlloc' with a size to
// guarantee that no garbage collection will happen (and hence nothing
// will move) until at least size bytes have been allocated.
// idris_doneAlloc *must* be called when allocation from C is done (as it
// may take a lock if other threads are running).

void idris_requireAlloc(VM *, size_t size);
void idris_doneAlloc(VM *);

// public interface to allocation (note that this may move other pointers
// if allocating beyond the limits given by idris_requireAlloc!)
// 'realloc' just calls alloc and copies; 'free' does nothing
void* idris_alloc(size_t size);
void* idris_realloc(void* old, size_t old_size, size_t size);
void idris_free(void* ptr, size_t size);

static inline void updateConF(Con * cl, unsigned tag, unsigned arity) {
    SETTY(cl, CT_CON);
    cl->tag = tag;
    // hdr.u16 used to store arity
    cl->hdr.u16 = arity;
    assert(cl->hdr.sz == sizeof(*cl) + sizeof(VAL) * arity);
    // cl->hdr.sz = sizeof(*cl) + sizeof(VAL) * arity;
}

static inline Con * allocConF(VM * vm, unsigned tag, unsigned arity, int outer) {
    Con * cl = iallocate(vm, sizeof(*cl) + sizeof(VAL) * arity, outer);
    SETTY(cl, CT_CON);
    cl->tag = tag;
    // hdr.u16 used to store arity
    cl->hdr.u16 = arity;
    return cl;
}

static inline Array * allocArrayF(VM * vm, size_t len, int outer) {
    Array * cl = iallocate(vm, sizeof(*cl) + sizeof(VAL) * len, outer);
    SETTY(cl, CT_ARRAY);
    return cl;
}


#define allocCon(cl, vm, t, a, o) (cl) = (VAL)allocConF(vm, t, a, o)

#define updateCon(cl, old, tag, arity) (cl) = (old); updateConF(cl, tag, arity)

#define NULL_CON(x) ((VAL)(nullary_cons + x))

#define allocArray(cl, vm, len, o) (cl) = (VAL)allocArrayF(vm, len, o)

int idris_errno(void);
char* idris_showerror(int err);

extern Con nullary_cons[];
void init_nullaries(void);

void init_signals(void);

void* vmThread(VM* callvm, func f, VAL arg);
void* idris_stopThread(VM* vm);

// Copy a structure to another vm's heap
VAL copyTo(VM* newVM, VAL x);

// Add a message to another VM's message queue
int idris_sendMessage(VM* sender, int channel_id, VM* dest, VAL msg);
// Check whether there are any messages in the queue and return PID of
// sender if so (null if not)
VM* idris_checkMessages(VM* vm);
// Check whether there are any messages which are initiating a conversation
// in the queue and return the message if so (without removing it)
Msg* idris_checkInitMessages(VM* vm);
// Check whether there are any messages in the queue
VM* idris_checkMessagesFrom(VM* vm, int channel_id, VM* sender);
// Check whether there are any messages in the queue, and wait if not
VM* idris_checkMessagesTimeout(VM* vm, int timeout);
// block until there is a message in the queue
Msg* idris_recvMessage(VM* vm);
// block until there is a message in the queue
Msg* idris_recvMessageFrom(VM* vm, int channel_id, VM* sender);

// Query/free structure used to return message data (recvMessage will malloc,
// so needs an explicit free)
VAL idris_getMsg(Msg* msg);
VM* idris_getSender(Msg* msg);
int idris_getChannel(Msg* msg);
void idris_freeMsg(Msg* msg);

void idris_trace(VM* vm, const char* func, int line);
void dumpVal(VAL r);
void dumpStack(VM* vm);

// Casts
#define idris_castIntFloat(x) MKFLOAT(vm, (double)(GETINT(x)))
#define idris_castFloatInt(x) MKINT((i_int)(GETFLOAT(x)))

VAL idris_castIntStr(VM* vm, VAL i);
VAL idris_castBitsStr(VM* vm, VAL i);
VAL idris_castStrInt(VM* vm, VAL i);
VAL idris_castFloatStr(VM* vm, VAL i);
VAL idris_castStrFloat(VM* vm, VAL i);

// Raw memory manipulation
void idris_memset(void* ptr, i_int offset, uint8_t c, i_int size);
void idris_memmove(void* dest, void* src, i_int dest_offset, i_int src_offset, i_int size);
uint8_t idris_peek(void* ptr, i_int offset);
void idris_poke(void* ptr, i_int offset, uint8_t data);

VAL idris_peekPtr(VM* vm, VAL ptr, VAL offset);
VAL idris_pokePtr(VAL ptr, VAL offset, VAL data);
VAL idris_peekDouble(VM* vm, VAL ptr, VAL offset);
VAL idris_pokeDouble(VAL ptr, VAL offset, VAL data);
VAL idris_peekSingle(VM* vm, VAL ptr, VAL offset);
VAL idris_pokeSingle(VAL ptr, VAL offset, VAL data);

// Crash with a message (used for partial primitives)
void idris_crash(char* msg);

// String primitives
VAL idris_concat(VM* vm, VAL l, VAL r);
VAL idris_strlt(VM* vm, VAL l, VAL r);
VAL idris_streq(VM* vm, VAL l, VAL r);
VAL idris_strlen(VM* vm, VAL l);
// Read a line from a file
VAL idris_readStr(VM* vm, FILE* h);
// Read up to 'num' characters from a file
VAL idris_readChars(VM* vm, int num, FILE* h);

VAL idris_strHead(VM* vm, VAL str);
VAL idris_strShift(VM* vm, VAL str, int num);
VAL idris_strTail(VM* vm, VAL str);
// This is not expected to be efficient! Mostly we wouldn't expect to call
// it at all at run time.
VAL idris_strCons(VM* vm, VAL x, VAL xs);
VAL idris_strIndex(VM* vm, VAL str, VAL i);
VAL idris_strRev(VM* vm, VAL str);
VAL idris_substr(VM* vm, VAL offset, VAL length, VAL str);

// Support for IORefs
VAL idris_newRefLock(VAL x, int outerlock);
VAL idris_newRef(VAL x);
void idris_writeRef(VAL ref, VAL x);
VAL idris_readRef(VAL ref);

// Support for IOArrays
VAL idris_newArray(VM* vm, int size, VAL def);
void idris_arraySet(VAL arr, int index, VAL newval);
VAL idris_arrayGet(VAL arr, int index);

// system infox
// used indices:
//   0 returns backend
//   1 returns OS
VAL idris_systemInfo(VM* vm, VAL index);

// Command line args

extern int __idris_argc;
extern char **__idris_argv;

int idris_numArgs(void);
const char *idris_getArg(int i);

// disable stdin/stdout buffering
void idris_disableBuffering(void);

#ifndef SEL4
int idris_usleep(int usec);
#endif // SEL4

// Handle stack overflow.
// Just reports an error and exits.

void stackOverflow(void);

// I think these names are nicer for an API...

#define idris_constructor allocCon
#define idris_setConArg SETARG
#define idris_getConArg GETARG
#define idris_mkInt(x) MKINT((intptr_t)(x))

#include "idris_gmp.h"

static inline size_t valSize(VAL v) {
    return v->hdr.sz;
}

static inline size_t aligned(size_t sz) {
    return (sz + sizeof(void*) - 1) & ~(sizeof(void*)-1);
}

VM* get_vm(void);

#endif

/*
  Local variables: **
  c-file-style: "bsd" **
  c-basic-offset: 4 **
  indent-tabs-mode: nil **
  End: **
*/
