#include <assert.h>
#include <errno.h>

#include "idris_rts.h"
#include "idris_gc.h"
#include "idris_utf8.h"
#include "idris_bitstring.h"
#include "getline.h"

#define STATIC_ASSERT(COND,MSG) typedef char static_assertion_##MSG[(COND)?1:-1]

STATIC_ASSERT(sizeof(Hdr) == 8, condSizeOfHdr);

#if defined(__linux__) || defined(__APPLE__) || defined(__FreeBSD__) || defined(__DragonFly__)
#include <signal.h>
#endif


#ifdef HAS_PTHREAD
static pthread_key_t vm_key;
#else
static VM* global_vm;
#endif

void free_key(void *vvm) {
    // nothing to free, we just used the VM pointer which is freed elsewhere
}

VM* init_vm(int stack_size, size_t heap_size,
            int max_threads // not implemented yet
            ) {

    VM* vm = malloc(sizeof(VM));
    STATS_INIT_STATS(vm->stats)
    STATS_ENTER_INIT(vm->stats)

    VAL* valstack = malloc(stack_size * sizeof(VAL));

    vm->active = 1;
    vm->valstack = valstack;
    vm->valstack_top = valstack;
    vm->valstack_base = valstack;
    vm->stack_max = valstack + stack_size;

    alloc_heap(&(vm->heap), heap_size, heap_size, NULL);

    c_heap_init(&vm->c_heap);

    vm->ret = NULL;
    vm->reg1 = NULL;
#ifdef HAS_PTHREAD
    vm->inbox = malloc(1024*sizeof(VAL));
    memset(vm->inbox, 0, 1024*sizeof(VAL));
    vm->inbox_end = vm->inbox + 1024;
    vm->inbox_write = vm->inbox;
    vm->inbox_nextid = 1;

    // The allocation lock must be reentrant. The lock exists to ensure that
    // no memory is allocated during the message sending process, but we also
    // check the lock in calls to allocate.
    // The problem comes when we use requireAlloc to guarantee a chunk of memory
    // first: this sets the lock, and since it is not reentrant, we get a deadlock.
    pthread_mutexattr_t rec_attr;
    pthread_mutexattr_init(&rec_attr);
    pthread_mutexattr_settype(&rec_attr, PTHREAD_MUTEX_RECURSIVE);

    pthread_mutex_init(&(vm->inbox_lock), NULL);
    pthread_mutex_init(&(vm->inbox_block), NULL);
    pthread_mutex_init(&(vm->alloc_lock), &rec_attr);
    pthread_cond_init(&(vm->inbox_waiting), NULL);

    vm->max_threads = max_threads;
    vm->processes = 0;

#else
    global_vm = vm;
#endif
    STATS_LEAVE_INIT(vm->stats)
    return vm;
}

VM* idris_vm(void) {
    VM* vm = init_vm(4096000, 4096000, 1);
    init_threadkeys();
    init_threaddata(vm);
    init_gmpalloc();
    init_nullaries();
    init_signals();

    return vm;
}

VM* get_vm(void) {
#ifdef HAS_PTHREAD
    return pthread_getspecific(vm_key);
#else
    return global_vm;
#endif
}

void close_vm(VM* vm) {
    terminate(vm);
}

#ifdef HAS_PTHREAD
void create_key(void) {
    pthread_key_create(&vm_key, free_key);
}
#endif

void init_threadkeys(void) {
#ifdef HAS_PTHREAD
    static pthread_once_t key_once = PTHREAD_ONCE_INIT;
    pthread_once(&key_once, create_key);
#endif
}

void init_threaddata(VM *vm) {
#ifdef HAS_PTHREAD
    pthread_setspecific(vm_key, vm);
#endif
}

void init_signals(void) {
#if defined(__linux__) || defined(__APPLE__) || defined(__FreeBSD__) || defined(__DragonFly__)
    signal(SIGPIPE, SIG_IGN);
#endif
}

Stats terminate(VM* vm) {
    Stats stats = vm->stats;
    STATS_ENTER_EXIT(stats)
#ifdef HAS_PTHREAD
    free(vm->inbox);
#endif
    free(vm->valstack);
    free_heap(&(vm->heap));
    c_heap_destroy(&(vm->c_heap));
#ifdef HAS_PTHREAD
    pthread_mutex_destroy(&(vm -> inbox_lock));
    pthread_mutex_destroy(&(vm -> inbox_block));
    pthread_cond_destroy(&(vm -> inbox_waiting));
#endif
    // free(vm);
    // Set the VM as inactive, so that if any message gets sent to it
    // it will not get there, rather than crash the entire system.
    // (TODO: We really need to be cleverer than this if we're going to
    // write programs than create lots of threads...)
    vm->active = 0;

    STATS_LEAVE_EXIT(stats)
    return stats;
}

CData cdata_allocate(size_t size, CDataFinalizer finalizer)
{
    void * data = (void *) malloc(size);
    return cdata_manage(data, size, finalizer);
}

CData cdata_manage(void * data, size_t size, CDataFinalizer finalizer)
{
    return c_heap_create_item(data, size, finalizer);
}

void idris_requireAlloc(VM * vm, size_t size) {
    if (!(vm->heap.next + size < vm->heap.end)) {
        idris_gc(vm);
    }
#ifdef HAS_PTHREAD
    int lock = vm->processes > 0;
    if (lock) { // We only need to lock if we're in concurrent mode
       pthread_mutex_lock(&vm->alloc_lock);
    }
#endif
}

void idris_doneAlloc(VM * vm) {
#ifdef HAS_PTHREAD
    int lock = vm->processes > 0;
    if (lock) { // We only need to lock if we're in concurrent mode
       pthread_mutex_unlock(&vm->alloc_lock);
    }
#endif
}

int space(VM* vm, size_t size) {
    return (vm->heap.next + size) < vm->heap.end;
}

void* idris_alloc(size_t size) {
    RawData * cl = (RawData*) allocate(sizeof(*cl)+size, 0);
    SETTY(cl, CT_RAWDATA);
    return (void*)cl->raw;
}

void* idris_realloc(void* old, size_t old_size, size_t size) {
    void* ptr = idris_alloc(size);
    memcpy(ptr, old, old_size);
    return ptr;
}

void idris_free(void* ptr, size_t size) {
}

void * allocate(size_t sz, int lock) {
    return iallocate(get_vm(), sz, lock);
}

void* iallocate(VM * vm, size_t isize, int outerlock) {
//    return malloc(size);
    size_t size = aligned(isize);

#ifdef HAS_PTHREAD
    int lock = vm->processes > 0 && !outerlock;

    if (lock) { // not message passing
       pthread_mutex_lock(&vm->alloc_lock);
    }
#endif

    if (vm->heap.next + size < vm->heap.end) {
        STATS_ALLOC(vm->stats, size)
        char* ptr = vm->heap.next;
        vm->heap.next += size;
        assert(vm->heap.next <= vm->heap.end);
        memset(ptr, 0, size);
        ((Hdr*)ptr)->sz = isize;

#ifdef HAS_PTHREAD
        if (lock) { // not message passing
           pthread_mutex_unlock(&vm->alloc_lock);
        }
#endif
        return (void*)ptr;
    } else {
        // If we're trying to allocate something bigger than the heap,
        // grow the heap here so that the new heap is big enough.
        if (size > vm->heap.size) {
            vm->heap.size += size;
        }
        idris_gc(vm);
#ifdef HAS_PTHREAD
        if (lock) { // not message passing
           pthread_mutex_unlock(&vm->alloc_lock);
        }
#endif
        return iallocate(vm, size, outerlock);
    }

}

static String * allocStr(VM * vm, size_t len, int outer) {
    String * cl = iallocate(vm, sizeof(*cl) + len + 1, outer);
    SETTY(cl, CT_STRING);
    cl->slen = len;
    return cl;
}

static VAL mkfloat(VM* vm, double val, int outer) {
    Float * cl = iallocate(vm, sizeof(*cl), outer);
    SETTY(cl, CT_FLOAT);
    cl->f = val;
    return (VAL)cl;
}

VAL MKFLOAT(VM* vm, double val) {
    return mkfloat(vm, val, 0);
}

VAL MKFLOATc(VM* vm, double val) {
    return mkfloat(vm, val, 1);
}

static VAL mkstrlen(VM* vm, const char * str, size_t len, int outer) {
    String * cl = allocStr(vm, len, outer);
    // hdr.u8 used to mark a null string
    cl->hdr.u8 = str == NULL;
    memcpy(cl->str, str, len);
    return (VAL)cl;
}

VAL MKSTRlen(VM* vm, const char * str, size_t len) {
    return mkstrlen(vm, str, len, 0);
}

VAL MKSTRclen(VM* vm, char* str, size_t len) {
    return mkstrlen(vm, str, len, 1);
}

VAL MKSTR(VM* vm, const char* str) {
    return mkstrlen(vm, str, str? strlen(str) : 0, 0);
}

VAL MKSTRc(VM* vm, char* str) {
    return mkstrlen(vm, str, strlen(str), 1);
}

static char * getstroff(StrOffset * stroff) {
    return stroff->base->str + stroff->offset;
}

char* GETSTROFF(VAL stroff) {
    // Assume STROFF
    return getstroff((StrOffset*)stroff);
}

static size_t getstrofflen(StrOffset * stroff) {
    return stroff->base->slen - stroff->offset;
}

size_t GETSTROFFLEN(VAL stroff) {
    // Assume STROFF
    // we're working in char* here so no worries about utf8 char length
    return getstrofflen((StrOffset*)stroff);
}

static VAL mkcdata(VM * vm, CHeapItem * item, int outer) {
    c_heap_insert_if_needed(vm, &vm->c_heap, item);
    CDataC * cl = iallocate(vm, sizeof(*cl), outer);
    SETTY(cl, CT_CDATA);
    cl->item = item;
    return (VAL)cl;
}

VAL MKCDATA(VM* vm, CHeapItem * item) {
    return mkcdata(vm, item, 0);
}

VAL MKCDATAc(VM* vm, CHeapItem * item) {
    return mkcdata(vm, item, 1);
}

static VAL mkptr(VM* vm, void* ptr, int outer) {
    Ptr * cl = iallocate(vm, sizeof(*cl), outer);
    SETTY(cl, CT_PTR);
    cl->ptr = ptr;
    return (VAL)cl;
}

VAL MKPTR(VM* vm, void* ptr) {
    return mkptr(vm, ptr, 0);
}

VAL MKPTRc(VM* vm, void* ptr) {
    return mkptr(vm, ptr, 1);
}

VAL mkmptr(VM* vm, void* ptr, size_t size, int outer) {
    ManagedPtr * cl = iallocate(vm, sizeof(*cl) + size, outer);
    SETTY(cl, CT_MANAGEDPTR);
    memcpy(cl->mptr, ptr, size);
    return (VAL)cl;
}

VAL MKMPTR(VM* vm, void* ptr, size_t size) {
    return mkmptr(vm, ptr, size, 0);
}

VAL MKMPTRc(VM* vm, void* ptr, size_t size) {
    return mkmptr(vm, ptr, size, 1);
}

VAL MKB8(VM* vm, uint8_t bits8) {
    Bits8 * cl = iallocate(vm, sizeof(*cl), 1);
    SETTY(cl, CT_BITS8);
    cl->bits8 = bits8;
    return (VAL)cl;
}

VAL MKB16(VM* vm, uint16_t bits16) {
    Bits16 * cl = iallocate(vm, sizeof(*cl), 1);
    SETTY(cl, CT_BITS16);
    cl->bits16 = bits16;
    return (VAL)cl;
}

VAL MKB32(VM* vm, uint32_t bits32) {
    Bits32 * cl = iallocate(vm, sizeof(*cl), 1);
    SETTY(cl, CT_BITS32);
    cl->bits32 = bits32;
    return (VAL)cl;
}

VAL MKB64(VM* vm, uint64_t bits64) {
    Bits64 * cl = iallocate(vm, sizeof(*cl), 1);
    SETTY(cl, CT_BITS64);
    cl->bits64 = bits64;
    return (VAL)cl;
}

void idris_trace(VM* vm, const char* func, int line) {
    printf("At %s:%d\n", func, line);
    dumpStack(vm);
    puts("");
    fflush(stdout);
}

void dumpStack(VM* vm) {
    int i = 0;
    VAL* root;

    for (root = vm->valstack; root < vm->valstack_top; ++root, ++i) {
        printf("%d: ", i);
        dumpVal(*root);
        if (*root >= (VAL)(vm->heap.heap) && *root < (VAL)(vm->heap.end)) { printf(" OK"); }
        if (root == vm->valstack_base) { printf(" <--- base"); }
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
    case CT_CON:
        {
            Con * cl = (Con*)v;
            printf("%d[", (int)TAG(cl));
            for(i = 0; i < CARITY(cl); ++i) {
                dumpVal(cl->args[i]);
            }
            printf("] ");
        }
        break;
    case CT_STRING:
        {
            String * cl = (String*)v;
            printf("STR[%s]", cl->str);
        }
        break;
    case CT_STROFFSET:
        {
            StrOffset * cl = (StrOffset*)v;
            printf("OFFSET[");
            dumpVal((VAL)cl->base);
            printf("]");
        }
        break;
    case CT_FWD:
        {
            Fwd * cl = (Fwd*)v;
            printf("CT_FWD ");
            dumpVal((VAL)cl->fwd);
        }
        break;
    default:
        printf("val");
    }

}

void idris_memset(void* ptr, i_int offset, uint8_t c, i_int size) {
    memset(((uint8_t*)ptr) + offset, c, size);
}

uint8_t idris_peek(void* ptr, i_int offset) {
    return *(((uint8_t*)ptr) + offset);
}

void idris_poke(void* ptr, i_int offset, uint8_t data) {
    *(((uint8_t*)ptr) + offset) = data;
}


VAL idris_peekPtr(VM* vm, VAL ptr, VAL offset) {
    void** addr = (void **)(((char *)GETPTR(ptr)) + GETINT(offset));
    return MKPTR(vm, *addr);
}

VAL idris_pokePtr(VAL ptr, VAL offset, VAL data) {
    void** addr = (void **)((char *)GETPTR(ptr) + GETINT(offset));
    *addr = GETPTR(data);
    return MKINT(0);
}

VAL idris_peekDouble(VM* vm, VAL ptr, VAL offset) {
    return MKFLOAT(vm, *(double*)((char *)GETPTR(ptr) + GETINT(offset)));
}

VAL idris_pokeDouble(VAL ptr, VAL offset, VAL data) {
    *(double*)((char *)GETPTR(ptr) + GETINT(offset)) = GETFLOAT(data);
    return MKINT(0);
}

VAL idris_peekSingle(VM* vm, VAL ptr, VAL offset) {
    return MKFLOAT(vm, *(float*)((char *)GETPTR(ptr) + GETINT(offset)));
}

VAL idris_pokeSingle(VAL ptr, VAL offset, VAL data) {
    *(float*)((char *)GETPTR(ptr) + GETINT(offset)) = GETFLOAT(data);
    return MKINT(0);
}

void idris_memmove(void* dest, void* src, i_int dest_offset, i_int src_offset, i_int size) {
    memmove((char *)dest + dest_offset, (char *)src + src_offset, size);
}

VAL idris_castIntStr(VM* vm, VAL i) {
    int x = (int) GETINT(i);
    String * cl = allocStr(vm, 16, 0);
    cl->slen = sprintf(cl->str, "%d", x);
    return (VAL)cl;
}

VAL idris_castBitsStr(VM* vm, VAL i) {
    String * cl;
    ClosureType ty = GETTY(i);

    switch (ty) {
    case CT_BITS8:
        // max length 8 bit unsigned int str 3 chars (256)
        cl = allocStr(vm, 4, 0);
        cl->slen = sprintf(cl->str, "%" PRIu8, GETBITS8(i));
        break;
    case CT_BITS16:
        // max length 16 bit unsigned int str 5 chars (65,535)
        cl = allocStr(vm, 6, 0);
        cl->slen = sprintf(cl->str, "%" PRIu16, GETBITS16(i));
        break;
    case CT_BITS32:
        // max length 32 bit unsigned int str 10 chars (4,294,967,295)
        cl = allocStr(vm, 11, 0);
        cl->slen = sprintf(cl->str, "%" PRIu32, GETBITS32(i));
        break;
    case CT_BITS64:
        // max length 64 bit unsigned int str 20 chars (18,446,744,073,709,551,615)
        cl = allocStr(vm, 21, 0);
        cl->slen = sprintf(cl->str, "%" PRIu64, GETBITS64(i));
        break;
    default:
        fprintf(stderr, "Fatal Error: ClosureType %d, not an integer type", ty);
        exit(EXIT_FAILURE);
    }
    return (VAL)cl;
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
    String * cl = allocStr(vm, 32, 0);
    cl->slen = snprintf(cl->str, 32, "%.16g", GETFLOAT(i));
    return (VAL)cl;
}

VAL idris_castStrFloat(VM* vm, VAL i) {
    return MKFLOAT(vm, strtod(GETSTR(i), NULL));
}

VAL idris_concat(VM* vm, VAL l, VAL r) {
    char *rs = GETSTR(r);
    char *ls = GETSTR(l);
    size_t llen = GETSTRLEN(l);
    size_t rlen = GETSTRLEN(r);

    String * cl = allocStr(vm, llen + rlen, 0);
    memcpy(cl->str, ls, llen);
    memcpy(cl->str + llen, rs, rlen);
    return (VAL)cl;
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
    return MKINT((i_int)(idris_utf8_strlen(GETSTR(l))));
}

VAL idris_readStr(VM* vm, FILE* h) {
    VAL ret;
    char *buffer = NULL;
    size_t n = 0;
    ssize_t len;
    len = getline(&buffer, &n, h);
    if (len <= 0) {
        ret = MKSTR(vm, "");
    } else {
        ret = MKSTR(vm, buffer);
    }
    free(buffer);
    return ret;
}

VAL idris_readChars(VM* vm, int num, FILE* h) {
    VAL ret;
    char *buffer = malloc((num+1)*sizeof(char));
    size_t len;
    len = fread(buffer, sizeof(char), (size_t)num, h);
    buffer[len] = '\0';

    if (len <= 0) {
        ret = MKSTR(vm, "");
    } else {
        ret = MKSTR(vm, buffer);
    }
    free(buffer);
    return ret;
}

void idris_crash(char* msg) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
}

VAL idris_strHead(VM* vm, VAL str) {
    return idris_strIndex(vm, str, 0);
}

VAL MKSTROFFc(VM* vm, VAL basestr) {
    StrOffset * cl = iallocate(vm, sizeof(*cl), 1);
    SETTY(cl, CT_STROFFSET);
    cl->base = (String*)basestr;
    return (VAL)cl;
}

VAL idris_strShift(VM* vm, VAL str, int num) {
    size_t sz = sizeof(StrOffset);
    // If there's no room, just copy the string, or we'll have a problem after
    // gc moves str
    if (space(vm, sz)) {
        int offset = 0;
        StrOffset * root = (StrOffset*)str;
        StrOffset * cl = iallocate(vm, sz, 0);
        SETTY(cl, CT_STROFFSET);

        while(root!=NULL && !ISSTR(root)) { // find the root, carry on.
                              // In theory, at most one step here!
            offset += root->offset;
            root = (StrOffset*)root->base;
        }

        cl->base = (String*)root;
        cl->offset = offset+idris_utf8_findOffset(GETSTR(str), num);
        return (VAL)cl;
    } else {
        char* nstr = GETSTR(str);
        return MKSTR(vm, nstr+idris_utf8_charlen(nstr));
    }
}

VAL idris_strTail(VM* vm, VAL str) {
    return idris_strShift(vm, str, 1);
}

VAL idris_strCons(VM* vm, VAL x, VAL xs) {
    char *xstr = GETSTR(xs);
    int xval = GETINT(x);
    size_t xlen = GETSTRLEN(xs);
    String * cl;

    if (xval < 0x80) { // ASCII char
      cl = allocStr(vm, xlen + 1, 0);
        cl->str[0] = (char)(GETINT(x));
        memcpy(cl->str+1, xstr, xlen);
    } else {
        char *init = idris_utf8_fromChar(xval);
        size_t ilen = strlen(init);
        int newlen = ilen + xlen;
        cl = allocStr(vm, newlen, 0);
        memcpy(cl->str, init, ilen);
        memcpy(cl->str + ilen, xstr, xlen);
        free(init);
    }
    return (VAL)cl;
}

VAL idris_strIndex(VM* vm, VAL str, VAL i) {
    int idx = idris_utf8_index(GETSTR(str), GETINT(i));
    return MKINT((i_int)idx);
}

VAL idris_substr(VM* vm, VAL offset, VAL length, VAL str) {
    size_t offset_val = GETINT(offset);
    size_t length_val = GETINT(length);
    char* str_val = GETSTR(str);

    // If the substring is a suffix, use idris_strShift to avoid reallocating
    if (offset_val + length_val >= GETSTRLEN(str)) {
        return idris_strShift(vm, str, offset_val);
    }
    else {
        char *start = idris_utf8_advance(str_val, offset_val);
        char *end = idris_utf8_advance(start, length_val);
        size_t sz = end - start;
        String * newstr = allocStr(vm, sz, 0);
        memcpy(newstr->str, start, sz);
        newstr->str[sz] = '\0';
        return (VAL)newstr;
    }
}

VAL idris_strRev(VM* vm, VAL str) {
    char *xstr = GETSTR(str);
    size_t xlen = GETSTRLEN(str);

    String * cl = allocStr(vm, xlen, 0);
    idris_utf8_rev(xstr, cl->str);
    return (VAL)cl;
}

VAL idris_newRefLock(VAL x, int outerlock) {
    Ref * cl = allocate(sizeof(*cl), outerlock);
    SETTY(cl, CT_REF);
    cl->ref = x;
    return (VAL)cl;
}

VAL idris_newRef(VAL x) {
    return idris_newRefLock(x, 0);
}

void idris_writeRef(VAL ref, VAL x) {
    Ref * r = (Ref*)ref;
    r->ref = x;
    SETTY(ref, CT_REF);
}

VAL idris_readRef(VAL ref) {
    Ref * r = (Ref*)ref;
    return r->ref;
}

VAL idris_newArray(VM* vm, int size, VAL def) {
    Array * cl;
    int i;
    cl = allocArrayF(vm, size, 0);
    for(i=0; i<size; ++i) {
        cl->array[i] = def;
    }
    return (VAL)cl;
}

void idris_arraySet(VAL arr, int index, VAL newval) {
    Array * cl = (Array*)arr;
    cl->array[index] = newval;
}

VAL idris_arrayGet(VAL arr, int index) {
    Array * cl = (Array*)arr;
    return cl->array[index];
}

VAL idris_systemInfo(VM* vm, VAL index) {
    int i = GETINT(index);
    switch(i) {
        case 0: // backend
            return MKSTR(vm, "c");
        case 1:
            return MKSTR(vm, IDRIS_TARGET_OS);
        case 2:
            return MKSTR(vm, IDRIS_TARGET_TRIPLE);
    }
    return MKSTR(vm, "");
}

typedef struct {
    VM* vm; // thread's VM
    VM* callvm; // calling thread's VM
    func fn;
    VAL arg;
} ThreadData;

#ifdef HAS_PTHREAD
void* runThread(void* arg) {
    ThreadData* td = (ThreadData*)arg;
    VM* vm = td->vm;
    VM* callvm = td->callvm;

    init_threaddata(vm);

    TOP(0) = td->arg;
    BASETOP(0);
    ADDTOP(1);
    td->fn(vm, NULL);
    callvm->processes--;

    free(td);

    //    Stats stats =
    terminate(vm);
    //    aggregate_stats(&(td->vm->stats), &stats);
    return NULL;
}

void* vmThread(VM* callvm, func f, VAL arg) {
    VM* vm = init_vm(callvm->stack_max - callvm->valstack, callvm->heap.size,
                     callvm->max_threads);
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

    int ok = pthread_create(&t, &attr, runThread, td);
//    usleep(100);
    if (ok == 0) {
        return vm;
    } else {
        terminate(vm);
        return NULL;
    }
}

void* idris_stopThread(VM* vm) {
    close_vm(vm);
    pthread_exit(NULL);
    return NULL;
}

static VAL doCopyTo(VM* vm, VAL x);

static void copyArray(VM* vm, VAL * dst, VAL * src, size_t len) {
    size_t i;
    for(i = 0; i < len; ++i)
      dst[i] = doCopyTo(vm, src[i]);
}


// VM is assumed to be a different vm from the one x lives on

static VAL doCopyTo(VM* vm, VAL x) {
    int ar;
    VAL cl;
    if (x==NULL || ISINT(x)) {
        return x;
    }
    switch(GETTY(x)) {
    case CT_CDATA:
        cl = MKCDATAc(vm, GETCDATA(x));
        break;
    case CT_BIGINT:
        cl = MKBIGMc(vm, GETMPZ(x));
        break;
    case CT_CON:
        ar = CARITY(x);
        if (ar == 0 && CTAG(x) < 256) { // globally allocated
            cl = x;
        } else {
            Con * c = allocConF(vm, CTAG(x), ar, 1);
            copyArray(vm, c->args, ((Con*)x)->args, ar);
            cl = (VAL)c;
        }
        break;
    case CT_ARRAY: {
        size_t len = CELEM(x);
        Array * a = allocArrayF(vm, len, 1);
        copyArray(vm, a->array, ((Array*)x)->array, len);
        cl = (VAL)a;
    } break;
    case CT_STRING:
    case CT_FLOAT:
    case CT_PTR:
    case CT_MANAGEDPTR:
    case CT_BITS8:
    case CT_BITS16:
    case CT_BITS32:
    case CT_BITS64:
    case CT_RAWDATA:
        {
            cl = iallocate(vm, x->hdr.sz, 0);
            memcpy(cl, x, x->hdr.sz);
        }
        break;
    default:
        assert(0); // We're in trouble if this happens...
    }
    return cl;
}

VAL copyTo(VM* vm, VAL x) {
    VAL ret = doCopyTo(vm, x);
    return ret;
}

// Add a message to another VM's message queue
int idris_sendMessage(VM* sender, int channel_id, VM* dest, VAL msg) {
    // FIXME: If GC kicks in in the middle of the copy, we're in trouble.
    // Probably best check there is enough room in advance. (How?)

    // Also a problem if we're allocating at the same time as the
    // destination thread (which is very likely)
    // Should the inbox be a different memory space?

    // So: we try to copy, if a collection happens, we do the copy again
    // under the assumption there's enough space this time.

    if (dest->active == 0) { return 0; } // No VM to send to

    int gcs = dest->stats.collections;
    pthread_mutex_lock(&dest->alloc_lock);
    VAL dmsg = copyTo(dest, msg);
    pthread_mutex_unlock(&dest->alloc_lock);

    if (dest->stats.collections > gcs) {
        // a collection will have invalidated the copy
        pthread_mutex_lock(&dest->alloc_lock);
        dmsg = copyTo(dest, msg); // try again now there's room...
        pthread_mutex_unlock(&dest->alloc_lock);
    }

    pthread_mutex_lock(&(dest->inbox_lock));

    if (dest->inbox_write >= dest->inbox_end) {
        // FIXME: This is obviously bad in the long run. This should
        // either block, make the inbox bigger, or return an error code,
        // or possibly make it user configurable
        fprintf(stderr, "Inbox full");
        exit(-1);
    }

    dest->inbox_write->msg = dmsg;
    if (channel_id == 0) {
        // Set lowest bit to indicate this message is initiating a channel
        channel_id = 1 + ((dest->inbox_nextid++) << 1);
    } else {
        channel_id = channel_id << 1;
    }
    dest->inbox_write->channel_id = channel_id;

    dest->inbox_write->sender = sender;
    dest->inbox_write++;

    // Wake up the other thread
    pthread_mutex_lock(&dest->inbox_block);
    pthread_cond_signal(&dest->inbox_waiting);
    pthread_mutex_unlock(&dest->inbox_block);

//    printf("Sending [signalled]...\n");

    pthread_mutex_unlock(&(dest->inbox_lock));
//    printf("Sending [unlock]...\n");
    return channel_id >> 1;
}

VM* idris_checkMessages(VM* vm) {
    return idris_checkMessagesFrom(vm, 0, NULL);
}

Msg* idris_checkInitMessages(VM* vm) {
    Msg* msg;

    for (msg = vm->inbox; msg < vm->inbox_end && msg->msg != NULL; ++msg) {
        if (msg->channel_id && 1 == 1) { // init bit set
            return msg;
        }
    }
    return 0;
}

VM* idris_checkMessagesFrom(VM* vm, int channel_id, VM* sender) {
    Msg* msg;

    for (msg = vm->inbox; msg < vm->inbox_end && msg->msg != NULL; ++msg) {
        if (sender == NULL || msg->sender == sender) {
            if (channel_id == 0 || channel_id == msg->channel_id >> 1) {
                return msg->sender;
            }
        }
    }
    return 0;
}

VM* idris_checkMessagesTimeout(VM* vm, int delay) {
    VM* sender = idris_checkMessagesFrom(vm, 0, NULL);
    if (sender != NULL) {
        return sender;
    }

    struct timespec timeout;
    int status;

    // Wait either for a timeout or until we get a signal that a message
    // has arrived.
    pthread_mutex_lock(&vm->inbox_block);
    timeout.tv_sec = time (NULL) + delay;
    timeout.tv_nsec = 0;
    status = pthread_cond_timedwait(&vm->inbox_waiting, &vm->inbox_block,
                               &timeout);
    (void)(status); //don't emit 'unused' warning
    pthread_mutex_unlock(&vm->inbox_block);

    return idris_checkMessagesFrom(vm, 0, NULL);
}


Msg* idris_getMessageFrom(VM* vm, int channel_id, VM* sender) {
    Msg* msg;

    for (msg = vm->inbox; msg < vm->inbox_write; ++msg) {
        if (sender == NULL || msg->sender == sender) {
            if (channel_id == 0 || channel_id == msg->channel_id >> 1) {
                return msg;
            }
        }
    }
    return NULL;
}

// block until there is a message in the queue
Msg* idris_recvMessage(VM* vm) {
    return idris_recvMessageFrom(vm, 0, NULL);
}

Msg* idris_recvMessageFrom(VM* vm, int channel_id, VM* sender) {
    Msg* msg;
    Msg* ret = malloc(sizeof(Msg));

    struct timespec timeout;
    int status;

    if (sender && sender->active == 0) { return NULL; } // No VM to receive from

    pthread_mutex_lock(&vm->inbox_block);
    msg = idris_getMessageFrom(vm, channel_id, sender);

    while (msg == NULL) {
//        printf("No message yet\n");
//        printf("Waiting [lock]...\n");
        timeout.tv_sec = time (NULL) + 3;
        timeout.tv_nsec = 0;
        status = pthread_cond_timedwait(&vm->inbox_waiting, &vm->inbox_block,
                               &timeout);
        (void)(status); //don't emit 'unused' warning
//        printf("Waiting [unlock]... %d\n", status);
        msg = idris_getMessageFrom(vm, channel_id, sender);
    }
    pthread_mutex_unlock(&vm->inbox_block);

    if (msg != NULL) {
        ret->msg = msg->msg;
        ret->sender = msg->sender;

        pthread_mutex_lock(&(vm->inbox_lock));

        // Slide everything down after the message in the inbox,
        // Move the inbox_write pointer down, and clear the value at the
        // end - O(n) but it's easier since the message from a specific
        // sender could be anywhere in the inbox

        for(;msg < vm->inbox_write; ++msg) {
            if (msg+1 != vm->inbox_end) {
                msg->sender = (msg + 1)->sender;
                msg->msg = (msg + 1)->msg;
            }
        }

        vm->inbox_write->msg = NULL;
        vm->inbox_write->sender = NULL;
        vm->inbox_write--;

        pthread_mutex_unlock(&(vm->inbox_lock));
    } else {
        fprintf(stderr, "No messages waiting");
        exit(-1);
    }

    return ret;
}
#endif

VAL idris_getMsg(Msg* msg) {
    return msg->msg;
}

VM* idris_getSender(Msg* msg) {
    return msg->sender;
}

int idris_getChannel(Msg* msg) {
    return msg->channel_id >> 1;
}

void idris_freeMsg(Msg* msg) {
    free(msg);
}

int idris_errno(void) {
    return errno;
}

char* idris_showerror(int err) {
    return strerror(err);
}

Con nullary_cons[256];

void init_nullaries(void) {
    int i;
    for(i = 0; i < 256; ++i) {
        Con * cl = nullary_cons + i;
        cl->hdr.sz = sizeof(*cl);
        SETTY(cl, CT_CON);
        cl->tag = i;
    }
}

int __idris_argc;
char **__idris_argv;

int idris_numArgs(void) {
    return __idris_argc;
}

const char* idris_getArg(int i) {
    return __idris_argv[i];
}

void idris_disableBuffering(void) {
  setvbuf(stdin, NULL, _IONBF, 0);
  setvbuf(stdout, NULL, _IONBF, 0);
}

#ifndef SEL4
int idris_usleep(int usec) {
    struct timespec t;
    t.tv_sec = usec / 1000000;
    t.tv_nsec = (usec % 1000000) * 1000;

    return nanosleep(&t, NULL);
}
#endif // SEL4

void stackOverflow(void) {
  fprintf(stderr, "Stack overflow");
  exit(-1);
}
