#ifndef _CLOSURE_H
#define _CLOSURE_H


// Closures
typedef void* VAL;

typedef struct {
    VAL* valstack;
    int* intstack;
    double* floatstack;
    VAL* valstack_ptr;
    int* intstack_ptr;
    double* floatstack_ptr;
    void* heap;
    int stack_max;
    VAL ret;
} VM;

VM* init_vm(int stack_size, size_t heap_size);

// Functions all take a pointer to their VM, and return nothing.
typedef void(*func)(VM*);

#define EXTEND(n) if (vm->valstack_ptr-vm->valstack + n < vm -> stack_max) \
    { vm->valstack_ptr+=(n) } else { stackOverflow(vm); }
#define CLEAR(n) vm->valstack_ptr-=(n)
#define SLIDE(drop, keep)			\
    for (i=1; i<=keep; ++i) {			\
	*(vm->valstack_ptr-i-drop) = *(vm->valstack_ptr-i);	\
    }						\
    vm->valstack_ptr-=(drop)

typedef enum {
    THUNK, CON, INT, FLOAT, STRING, UNIT, PTR
} ClosureType;

typedef struct {
    VAL fn;
    int arity;
    int numargs;
    VAL* args;
} thunk;

typedef struct {
    int tag;
    VAL* args;
} con;

typedef struct {
    ClosureType ty;
    union {
        thunk t;
        con c;
        int i;
        double f;
        char* str;
        void* ptr;
    } info;
} Closure;

// Stack manipulation instructions

#define PUSH(i) *(vm->valstack_ptr++) = i;
#define POP --vm->valstack_ptr;

#define PUSHINT(i) *(vm->intstack_ptr++) = i;
#define POPINT --vm->intstack_ptr;

#define PUSHFLOAT(i) *(vm->floatstack_ptr++) = i;
#define POPFLOAT --vm->floatstack_ptr;

#define DISCARD(n) vm->valstack_ptr-=n;
#define DISCARDINT(n) vm->intstack_ptr-=n;
#define DISCARDFLOAT(n) vm->floatstack_ptr-=n;

// Creating new values (each value placed at the top of the stack)
VAL mkInt(VM* vm, int val);
VAL mkFloat(VM* vm, double val);
VAL mkStr(VM* vm, char* str);

VAL mkThunk(VM* vm, func fn, int args, int arity);
VAL mkCon(VM* vm, int tag, int arity);

void EVAL(int update);

// Handle stack overflow. 
// Just reports an error and exits.

void stackOverflow();

#endif 
