#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdarg.h>
#include <assert.h>
#include <pthread.h>

#include "idris_rts.h"
#include "idris_gc.h"

VM* init_vm(int stack_size, size_t heap_size, 
            int max_threads, // not implemented yet
            int argc, char* argv[]) {
    VAL* valstack = malloc(stack_size*sizeof(VAL));
    int* intstack = malloc(stack_size*sizeof(int));
    double* floatstack = malloc(stack_size*sizeof(double));

    VM* vm = malloc(sizeof(VM));
    vm->valstack = valstack;
    vm->valstack_top = valstack;
    vm->valstack_base = valstack;
    vm->intstack = intstack;
    vm->intstack_ptr = intstack;
    vm->floatstack = floatstack;
    vm->floatstack_ptr = floatstack;
    vm->stack_max = valstack + stack_size;
    vm->heap = malloc(heap_size);
    vm->oldheap = NULL;
    vm->heap_next = vm->heap;
    vm->heap_end = vm->heap + heap_size;
    vm->heap_size = heap_size;
    vm->collections = 0;
    vm->allocations = 0;
    vm->heap_growth = heap_size;
    vm->ret = NULL;
    vm->reg1 = NULL;

    vm->inbox = malloc(1024*sizeof(VAL));
    memset(vm->inbox, 0, 1024*sizeof(VAL));
    vm->inbox_end = vm->inbox + 1024;
    vm->inbox_ptr = vm->inbox;
    vm->inbox_write = vm->inbox;

    pthread_mutex_init(&(vm->inbox_lock), NULL);
    pthread_mutex_init(&(vm->inbox_block), NULL);
    pthread_mutex_init(&(vm->alloc_lock), NULL);
    pthread_cond_init(&(vm->inbox_waiting), NULL);

    vm->max_threads = max_threads;
    vm->processes = 0;

    int i;
    // Assumption: there's enough space for this in the initial heap.
    vm->argv = malloc(argc*sizeof(VAL));
    vm->argc = argc;

    for(i = 0; i < argc; ++i) {
        vm->argv[i] = MKSTR(vm, argv[i]);
    }

    return vm;
}

void terminate(VM* vm) {
    free(vm->inbox);
    free(vm->valstack);
    free(vm->intstack);
    free(vm->floatstack);
    free(vm->heap);
    free(vm->argv);
    if (vm->oldheap != NULL) { free(vm->oldheap); }
    pthread_mutex_destroy(&(vm -> inbox_lock));
    pthread_mutex_destroy(&(vm -> inbox_block));
    pthread_cond_destroy(&(vm -> inbox_waiting));
    free(vm);
}

void* allocate(VM* vm, size_t size, int outerlock) {
//    return malloc(size);
    int lock = vm->processes > 0 && !outerlock;

    if (lock) { // not message passing
       pthread_mutex_lock(&vm->alloc_lock); 
    }

    if ((size & 7)!=0) {
	size = 8 + ((size >> 3) << 3);
    }
    if (vm -> heap_next + size < vm -> heap_end) {
        vm->allocations += size + sizeof(size_t);
        void* ptr = (void*)(vm->heap_next + sizeof(size_t));
        *((size_t*)(vm->heap_next)) = size + sizeof(size_t);
        vm -> heap_next += size + sizeof(size_t);
        memset(ptr, 0, size);
        if (lock) { // not message passing
           pthread_mutex_unlock(&vm->alloc_lock); 
        }
        return ptr;
    } else {
        idris_gc(vm);
        if (lock) { // not message passing
           pthread_mutex_unlock(&vm->alloc_lock); 
        }
        return allocate(vm, size, 0);
    }

}

/* Now a macro
void* allocCon(VM* vm, int arity, int outer) {
    Closure* cl = allocate(vm, sizeof(Closure) + sizeof(VAL)*arity,
                               outer);
    SETTY(cl, CON);

    cl -> info.c.arity = arity;
//    cl -> info.c.tag = 42424242;
//    printf("%p\n", cl);
    return (void*)cl;
}
*/

VAL MKFLOAT(VM* vm, double val) {
    Closure* cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, FLOAT);
    cl -> info.f = val;
    return cl;
}

VAL MKSTR(VM* vm, char* str) {
    Closure* cl = allocate(vm, sizeof(Closure) + // Type) + sizeof(char*) +
                               sizeof(char)*strlen(str)+1, 0);
    SETTY(cl, STRING);
    cl -> info.str = (char*)cl + sizeof(Closure);

    strcpy(cl -> info.str, str);
    return cl;
}

VAL MKPTR(VM* vm, void* ptr) {
    Closure* cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, PTR);
    cl -> info.ptr = ptr;
    return cl;
}

VAL MKFLOATc(VM* vm, double val) {
    Closure* cl = allocate(vm, sizeof(Closure), 1);
    SETTY(cl, FLOAT);
    cl -> info.f = val;
    return cl;
}

VAL MKSTRc(VM* vm, char* str) {
    Closure* cl = allocate(vm, sizeof(Closure) + // Type) + sizeof(char*) +
                               sizeof(char)*strlen(str)+1, 1);
    SETTY(cl, STRING);
    cl -> info.str = (char*)cl + sizeof(Closure);

    strcpy(cl -> info.str, str);
    return cl;
}

VAL MKPTRc(VM* vm, void* ptr) {
    Closure* cl = allocate(vm, sizeof(Closure), 1);
    SETTY(cl, PTR);
    cl -> info.ptr = ptr;
    return cl;
}

void PROJECT(VM* vm, VAL r, int loc, int arity) {
    int i;
    for(i = 0; i < arity; ++i) {
        LOC(i+loc) = r->info.c.args[i];
    }
}

void SLIDE(VM* vm, int args) {
    int i;
    for(i = 0; i < args; ++i) {
        LOC(i) = TOP(i);
    }
}

void dumpStack(VM* vm) {
    int i = 0;
    VAL* root;

    for (root = vm->valstack; root < vm->valstack_top; ++root, ++i) {
        printf("%d: ", i);
        dumpVal(*root);
        if (*root >= (VAL)(vm->heap) && *root < (VAL)(vm->heap_end)) { printf("OK"); }
        printf("\n");
    }
    printf("RET: ");
    dumpVal(vm->ret);
    printf("\n");
}

void dumpVal(VAL v) {
    if (v==NULL) return;
    int i;
    if (ISINT(v)) { 
        printf("%d ", (int)(GETINT(v)));
        return;
    }
    switch(GETTY(v)) {
    case CON:
        printf("%d[", TAG(v));
        for(i = 0; i < ARITY(v); ++i) {
            dumpVal(v->info.c.args[i]);
        }
        printf("] ");
        break;
    case STRING:
        printf("STR[%s]", v->info.str);
        break;
    case FWD:
        printf("FWD ");
        dumpVal((VAL)(v->info.ptr));
        break;
    default:
        printf("val");
    }

}

VAL idris_castIntStr(VM* vm, VAL i) {
    Closure* cl = allocate(vm, sizeof(Closure) + sizeof(char)*16, 0);
    SETTY(cl, STRING);
    cl -> info.str = (char*)cl + sizeof(Closure);
    sprintf(cl -> info.str, "%d", (int)(GETINT(i)));
    return cl;
}

VAL idris_castStrInt(VM* vm, VAL i) {
    char *end;
    i_int v = strtol(GETSTR(i), &end, 10);
    if (*end == '\0' || *end == '\n' || *end == '\r') 
        return MKINT(v);
    else 
        return MKINT(0); 
}

VAL idris_castFloatStr(VM* vm, VAL i) {
    Closure* cl = allocate(vm, sizeof(Closure) + sizeof(char)*32, 0);
    SETTY(cl, STRING);
    cl -> info.str = (char*)cl + sizeof(Closure);
    sprintf(cl -> info.str, "%g", GETFLOAT(i));
    return cl;
}

VAL idris_castStrFloat(VM* vm, VAL i) {
    return MKFLOAT(vm, strtod(GETSTR(i), NULL));
}

VAL idris_concat(VM* vm, VAL l, VAL r) {
    char *rs = GETSTR(r);
    char *ls = GETSTR(l);
    // dumpVal(l);
    // printf("\n");
    Closure* cl = allocate(vm, sizeof(Closure) + strlen(ls) + strlen(rs) + 1,
                               0);
    SETTY(cl, STRING);
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

VAL idris_strHead(VM* vm, VAL str) {
    return MKINT((i_int)(GETSTR(str)[0]));
}

VAL idris_strTail(VM* vm, VAL str) {
    return MKSTR(vm, GETSTR(str)+1);
}

VAL idris_strCons(VM* vm, VAL x, VAL xs) {
    char *xstr = GETSTR(xs);
    Closure* cl = allocate(vm, sizeof(Closure) +
                               strlen(xstr) + 2, 0);
    SETTY(cl, STRING);
    cl -> info.str = (char*)cl + sizeof(Closure);
    cl -> info.str[0] = (char)(GETINT(x));
    strcpy(cl -> info.str+1, xstr);
    return cl;
}

VAL idris_strIndex(VM* vm, VAL str, VAL i) {
    return MKINT((i_int)(GETSTR(str)[GETINT(i)]));
}

VAL idris_strRev(VM* vm, VAL str) {
    char *xstr = GETSTR(str);
    Closure* cl = allocate(vm, sizeof(Closure) +
                               strlen(xstr) + 1, 0);
    SETTY(cl, STRING);
    cl -> info.str = (char*)cl + sizeof(Closure);
    int y = 0;
    int x = strlen(xstr);

    cl-> info.str[x+1] = '\0';
    while(x>0) {
        cl -> info.str[y++] = xstr[--x];
    }
    return cl;
}

typedef struct {
    VM* vm; // thread's VM
    VM* callvm; // calling thread's VM
    func fn;
    VAL arg;
} ThreadData;

void* runThread(void* arg) {
    ThreadData* td = (ThreadData*)arg;
    VM* vm = td->vm;
    VM* callvm = td->callvm;

    TOP(0) = td->arg;
    BASETOP(0);
    ADDTOP(1);
    td->fn(vm, NULL);
    callvm->processes--;

    free(td);
    terminate(vm);
    return NULL;
}

void* vmThread(VM* callvm, func f, VAL arg) {
    VM* vm = init_vm(callvm->stack_max - callvm->valstack, callvm->heap_size, 
                     callvm->max_threads,
                     0, NULL);
    vm->processes=1; // since it can send and receive messages
    pthread_t t;
    pthread_attr_t attr;
//    size_t stacksize;

    pthread_attr_init(&attr);
//    pthread_attr_getstacksize (&attr, &stacksize);
//    pthread_attr_setstacksize (&attr, stacksize*64);

    ThreadData *td = malloc(sizeof(ThreadData));
    td->vm = vm;
    td->callvm = callvm;
    td->fn = f;
    td->arg = copyTo(vm, arg);
    
    callvm->processes++;

    pthread_create(&t, &attr, runThread, td);
//    usleep(100);
    return vm;
}

// VM is assumed to be a different vm from the one x lives on 

VAL copyTo(VM* vm, VAL x) {
    int i, ar;
    VAL* argptr;
    Closure* cl;
    if (x==NULL || ISINT(x)) {
        return x;
    }
    switch(GETTY(x)) {
    case CON:
        ar = CARITY(x);
        allocCon(cl, vm, CTAG(x), ar, 1);

        argptr = (VAL*)(cl->info.c.args);
        for(i = 0; i < ar; ++i) {
            *argptr = copyTo(vm, *((VAL*)(x->info.c.args)+i)); // recursive version
            argptr++;
        }
        break;
    case FLOAT:
        cl = MKFLOATc(vm, x->info.f);
        break;
    case STRING:
        cl = MKSTRc(vm, x->info.str);
        break;
    case BIGINT:
        cl = MKBIGMc(vm, x->info.ptr);
        break;
    case PTR:
        cl = MKPTRc(vm, x->info.ptr);
        break;
    default:
        assert(0); // We're in trouble if this happens...
    }
    return cl;
}

// Add a message to another VM's message queue
void idris_sendMessage(VM* sender, VM* dest, VAL msg) {
    // FIXME: If GC kicks in in the middle of the copy, we're in trouble.
    // Probably best check there is enough room in advance. (How?)

    // Also a problem if we're allocating at the same time as the 
    // destination thread (which is very likely)
    // Should the inbox be a different memory space?
    
    // So: we try to copy, if a collection happens, we do the copy again
    // under the assumption there's enough space this time.

    int gcs = dest->collections;
    pthread_mutex_lock(&dest->alloc_lock); 
    VAL dmsg = copyTo(dest, msg);
    pthread_mutex_unlock(&dest->alloc_lock); 

    if (dest->collections>gcs) {
        // a collection will have invalidated the copy
        pthread_mutex_lock(&dest->alloc_lock); 
        dmsg = copyTo(dest, msg); // try again now there's room...
        pthread_mutex_unlock(&dest->alloc_lock); 
    }

    pthread_mutex_lock(&(dest->inbox_lock));
    *(dest->inbox_write) = dmsg;
   
    dest->inbox_write++;
    if (dest->inbox_write >= dest->inbox_end) {
        dest->inbox_write = dest->inbox;
    }

    if (dest->inbox_write == dest->inbox_ptr) {
        fprintf(stderr, "Inbox full"); // Maybe grow it instead...
        exit(-1);
    }

    // Wake up the other thread
    pthread_mutex_lock(&dest->inbox_block);
    pthread_cond_signal(&dest->inbox_waiting);
    pthread_mutex_unlock(&dest->inbox_block);

//    printf("Sending [signalled]...\n");

    pthread_mutex_unlock(&(dest->inbox_lock));
//    printf("Sending [unlock]...\n");
}

int idris_checkMessages(VM* vm) {
    VAL msg = *(vm->inbox_ptr);
    return (msg != NULL);
}

// block until there is a message in the queue
VAL idris_recvMessage(VM* vm) {
    VAL msg;
    struct timespec timeout;
    int status;

    pthread_mutex_lock(&vm->inbox_block);
    msg = *(vm->inbox_ptr);
    while (msg == NULL) {
//        printf("No message yet\n");
//        printf("Waiting [lock]...\n");
        timeout.tv_sec = time (NULL) + 3;
        timeout.tv_nsec = 0;
        status = pthread_cond_timedwait(&vm->inbox_waiting, &vm->inbox_block,
                               &timeout);
        (void)(status); //don't emit 'unused' warning
//        printf("Waiting [unlock]... %d\n", status);
        msg = *(vm->inbox_ptr);
    }
    pthread_mutex_unlock(&vm->inbox_block);

    if (msg != NULL) {
        pthread_mutex_lock(&(vm->inbox_lock));
        *(vm->inbox_ptr) = NULL;
        vm->inbox_ptr++;
        if (vm->inbox_ptr >= vm->inbox_end) {
            vm->inbox_ptr = vm->inbox;
        }
        pthread_mutex_unlock(&(vm->inbox_lock));
    } else {
        fprintf(stderr, "No messages waiting");
        exit(-1);
    }

    return msg;
}

int idris_numArgs(VM* vm) {
    return vm->argc;
}

VAL idris_getArg(VM* vm, int i) {
    return vm->argv[i];
}

void stackOverflow() {
  fprintf(stderr, "Stack overflow");
  exit(-1);
}

