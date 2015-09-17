#include <assert.h>
#include <limits.h>
#include <ctype.h>

#include "idris_rts.h"
#include "idris_gc.h"
#include "idris_utf8.h"
#include "idris_bitstring.h"
#include "getline.h"

#ifdef HAS_PTHREAD
static pthread_key_t vm_key;
#else
static VM* global_vm;
#endif

void free_key(VM *vm) {
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

    vm->ret = NULL;
    vm->reg1 = NULL;
#ifdef HAS_PTHREAD
    vm->inbox = malloc(1024*sizeof(VAL));
    memset(vm->inbox, 0, 1024*sizeof(VAL));
    vm->inbox_end = vm->inbox + 1024;
    vm->inbox_write = vm->inbox;

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

VM* idris_vm() {
    VM* vm = init_vm(4096000, 4096000, 1);
    init_threadkeys();
    init_threaddata(vm);
    init_gmpalloc();
    init_nullaries();

    return vm;
}

void close_vm(VM* vm) {
    terminate(vm);
}

void init_threadkeys() {
#ifdef HAS_PTHREAD
    pthread_key_create(&vm_key, (void*)free_key);
#endif
}

void init_threaddata(VM *vm) {
#ifdef HAS_PTHREAD
    pthread_setspecific(vm_key, vm);
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

void idris_requireAlloc(size_t size) {
#ifdef HAS_PTHREAD
    VM* vm = pthread_getspecific(vm_key);
#else
    VM* vm = global_vm;
#endif

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

void idris_doneAlloc() {
#ifdef HAS_PTHREAD
    VM* vm = pthread_getspecific(vm_key);
    int lock = vm->processes > 0;
    if (lock) { // We only need to lock if we're in concurrent mode
       pthread_mutex_unlock(&vm->alloc_lock);
    }
#endif
}

int space(VM* vm, size_t size) {
    return (vm->heap.next + size + sizeof(size_t) < vm->heap.end);
}

void* idris_alloc(size_t size) {
    Closure* cl = (Closure*) allocate(sizeof(Closure) + size, 0);
    SETTY(cl, RAWDATA);
    cl->info.size = size;
    return (void*)cl + sizeof(Closure);
}

void* idris_realloc(void* old, size_t old_size, size_t size) {
    void* ptr = idris_alloc(size);
    memcpy(ptr, old, old_size);
    return ptr;
}

void idris_free(void* ptr, size_t size) {
}

void* allocate(size_t size, int outerlock) {
//    return malloc(size);

#ifdef HAS_PTHREAD
    VM* vm = pthread_getspecific(vm_key);
    int lock = vm->processes > 0 && !outerlock;

    if (lock) { // not message passing
       pthread_mutex_lock(&vm->alloc_lock);
    }
#else
    VM* vm = global_vm;
#endif

    if ((size & 7)!=0) {
	size = 8 + ((size >> 3) << 3);
    }

    size_t chunk_size = size + sizeof(size_t);

    if (vm->heap.next + chunk_size < vm->heap.end) {
        STATS_ALLOC(vm->stats, chunk_size)
        void* ptr = (void*)(vm->heap.next + sizeof(size_t));
        *((size_t*)(vm->heap.next)) = chunk_size;
        vm->heap.next += chunk_size;

        assert(vm->heap.next <= vm->heap.end);

        memset(ptr, 0, size);
#ifdef HAS_PTHREAD
        if (lock) { // not message passing
           pthread_mutex_unlock(&vm->alloc_lock);
        }
#endif
        return ptr;
    } else {
        idris_gc(vm);
#ifdef HAS_PTHREAD
        if (lock) { // not message passing
           pthread_mutex_unlock(&vm->alloc_lock);
        }
#endif
        return allocate(size, 0);
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
    Closure* cl = allocate(sizeof(Closure), 0);
    SETTY(cl, FLOAT);
    cl -> info.f = val;
    return cl;
}

Closure *idris_allocate_string(size_t size, int outerlock) {
    Closure* cl = allocate(sizeof(Closure) + // object header
                           sizeof(SizedString) + // string bookkeeping
                           sizeof(utf8_byte) * size + // the string data
                           sizeof(utf8_byte), // the null terminator
                           outerlock);
    SETTY(cl, STRING);
    cl -> info.str = (SizedString *) ((uint8_t *)cl + sizeof(Closure));
    cl -> info.str -> size = size;
    cl -> info.str -> str_data = (utf8_byte*)cl + sizeof(Closure) + sizeof(SizedString);
    // We keep the strings null-terminated to allow easier C interop without copying
    cl -> info.str -> str_data[size] = '\0';
    return cl;
}

VAL MKSTR(VM* vm, const utf8_byte* str) {
    if (str == NULL) {
        // We need to preserve NULLness so that things like getenv
        // work with the FFI as presently specified.
        Closure* cl = idris_allocate_string(0, 0);
        cl -> info.str -> str_data = NULL;
        return cl;
    } else {
        size_t len = idris_utf8_unitlen(str);
        Closure* cl = idris_allocate_string(len, 0);
        if (str != NULL) {
            memcpy(cl -> info.str -> str_data, str, len);
        }
        assert(cl -> info.str -> size == len);
        return cl;
    }
}

SizedString GETSTROFF(VAL stroff) {
    // Assume STROFF
    StrOffset* root = stroff->info.str_offset;
    SizedString with_offset = {
        .str_data = (utf8_byte *)(root ->str->info.str->str_data) + (root->offset),
        .size = root->str->info.str->size - root->offset
    };
    return with_offset;
}

char *idris_get_c_str(SizedString str) {
    return (char *) str.str_data;
}

VAL MKPTR(VM* vm, void* ptr) {
    Closure* cl = allocate(sizeof(Closure), 0);
    SETTY(cl, PTR);
    cl -> info.ptr = ptr;
    return cl;
}

VAL MKMPTR(VM* vm, void* ptr, size_t size) {
    Closure* cl = allocate(sizeof(Closure) +
                           sizeof(ManagedPtr) + size, 0);
    SETTY(cl, MANAGEDPTR);
    cl->info.mptr = (ManagedPtr*)((char*)cl + sizeof(Closure));
    cl->info.mptr->data = (char*)cl + sizeof(Closure) + sizeof(ManagedPtr);
    memcpy(cl->info.mptr->data, ptr, size);
    cl->info.mptr->size = size;
    return cl;
}

VAL MKFLOATc(VM* vm, double val) {
    Closure* cl = allocate(sizeof(Closure), 1);
    SETTY(cl, FLOAT);
    cl -> info.f = val;
    return cl;
}

VAL MKSTRc(VM* vm, SizedString* str) {
    Closure* cl = idris_allocate_string(str->size, 1);
    memcpy(cl -> info.str -> str_data, str->str_data, str->size);
    return cl;
}

VAL MKPTRc(VM* vm, void* ptr) {
    Closure* cl = allocate(sizeof(Closure), 1);
    SETTY(cl, PTR);
    cl -> info.ptr = ptr;
    return cl;
}

VAL MKMPTRc(VM* vm, void* ptr, size_t size) {
    Closure* cl = allocate(sizeof(Closure) +
                           sizeof(ManagedPtr) + size, 1);
    SETTY(cl, MANAGEDPTR);
    cl->info.mptr = (ManagedPtr*)((char*)cl + sizeof(Closure));
    cl->info.mptr->data = (char*)cl + sizeof(Closure) + sizeof(ManagedPtr);
    memcpy(cl->info.mptr->data, ptr, size);
    cl->info.mptr->size = size;
    return cl;
}

VAL MKB8(VM* vm, uint8_t bits8) {
    Closure* cl = allocate(sizeof(Closure), 1);
    SETTY(cl, BITS8);
    cl -> info.bits8 = bits8;
    return cl;
}

VAL MKB16(VM* vm, uint16_t bits16) {
    Closure* cl = allocate(sizeof(Closure), 1);
    SETTY(cl, BITS16);
    cl -> info.bits16 = bits16;
    return cl;
}

VAL MKB32(VM* vm, uint32_t bits32) {
    Closure* cl = allocate(sizeof(Closure), 1);
    SETTY(cl, BITS32);
    cl -> info.bits32 = bits32;
    return cl;
}

VAL MKB64(VM* vm, uint64_t bits64) {
    Closure* cl = allocate(sizeof(Closure), 1);
    SETTY(cl, BITS64);
    cl -> info.bits64 = bits64;
    return cl;
}

void PROJECT(VM* vm, VAL r, int loc, int arity) {
    int i;
    for(i = 0; i < arity; ++i) {
        LOC(i + loc) = r->info.c.args[i];
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
        if (*root >= (VAL)(vm->heap.heap) && *root < (VAL)(vm->heap.end)) { printf("OK"); }
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
        printf("STR(%lu)[%.*s]\n", v->info.str->size, (int)v->info.str->size, v->info.str->str_data);
        break;
    case STROFFSET:
        printf("STROFF(%lu)=\n\t", v->info.str_offset->offset);
        dumpVal(v->info.str_offset->str);
        break;
    case FWD:
        printf("FWD ");
        dumpVal((VAL)(v->info.ptr));
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

void idris_memmove(void* dest, void* src, i_int dest_offset, i_int src_offset, i_int size) {
    memmove(dest + dest_offset, src + src_offset, size);
}

VAL idris_castIntStr(VM* vm, VAL i) {
    // this is an overapproximation of what's needed to hold an int as a string
    // Each byte will take log_10(256) ~= 2.4 digits, so 4 digits per byte is
    // clearly enough. Then add 1 for the terminator.
    char temp[sizeof(int) * 4 + 1] = {0};
    int x = (int) GETINT(i);
    sprintf(temp, "%d", x);

    // avoid invalid UTF-8: all ASCII digits are acceptable as UTF-8 characters.
    unsigned int j;
    for (j = 0; j < sizeof(int) * 4 + 1; j++) {
        if (temp[j] != '\0' && !(isdigit(temp[j])) && temp[j] != '-') {
            fprintf(stderr, "Fatal error: invalid output from sprintf on an int!\n");
            fprintf(stderr, "It was [%c] at index [%u] in [%s].\n", temp[j], j, temp);
            exit(EXIT_FAILURE);
        }
    }

    return MKSTR(vm, (const utf8_byte*)temp);
}

VAL idris_castBitsStr(VM* vm, VAL i) {

    // max length 64 bit unsigned int str 20 chars (18,446,744,073,709,551,615)
    #define MAX_DIGITS_FOR_64_BITS 20
    ClosureType ty = i->ty;

    char temp[MAX_DIGITS_FOR_64_BITS + 1] = { 0 };

    switch (ty) {
    case BITS8:
        sprintf(temp, "%" PRIu8, (uint8_t)i->info.bits8);
        break;
    case BITS16:
        sprintf(temp, "%" PRIu16, (uint16_t)i->info.bits16);
        break;
    case BITS32:
        sprintf(temp, "%" PRIu32, (uint32_t)i->info.bits32);
        break;
    case BITS64:
        sprintf(temp, "%" PRIu64, (uint64_t)i->info.bits64);
        break;
    default:
        fprintf(stderr, "Fatal Error: ClosureType %d, not an integer type", ty);
        exit(EXIT_FAILURE);
    }

    // avoid invalid UTF-8: all ASCII digits are acceptable as UTF-8 characters.
    int j;
    for (j = 0; j < MAX_DIGITS_FOR_64_BITS + 1; j++) {
        if (temp[j] != '\0' && !(isdigit(temp[j]))) {
            fprintf(stderr, "Fatal error: invalid output from sprintf on bit type %d!", ty);
            exit(EXIT_FAILURE);
        }
    }

    return MKSTR(vm, (const utf8_byte *)temp);
}

VAL idris_castStrInt(VM* vm, VAL i) {
    char *end;
    SizedString str = GETSTR(i);

    // First, we need to alloc a C string that's long enough (to get null-termination)
    char *temp = (char *) malloc(str.size + 1);
    if (temp == NULL) {
        fprintf(stderr, "Couldn't allocate temp buffer of size %lu for int->string conversion", str.size);
        exit(EXIT_FAILURE);
    }
    // Then grab the UTF8 bytes out of the Idris string. We don't have
    // to worry about nulls in the middle because we'll later check to
    // see if the whole string was used.
    memcpy(temp, str.str_data, str.size);
    temp[str.size] = '\0';

    i_int v = strtol(temp, &end, 10);
    Closure* answer;
    // If we used the whole string, return the int, otherwise return 0. This is
    // the meaning of the primitive in the evaluator.
    if (end == temp + str.size)
        answer = MKINT(v);
    else
        answer = MKINT(0);
    free(temp);
    return answer;
}

VAL idris_castFloatStr(VM* vm, VAL i) {
    // Use a maximum of 31 digits to print floats here, plus 1 char for null
    const unsigned int MAX_CHARS_FOR_DOUBLE = 32;
    char temp[MAX_CHARS_FOR_DOUBLE];
    memset(temp, '\0', MAX_CHARS_FOR_DOUBLE);

    snprintf(temp, MAX_CHARS_FOR_DOUBLE, "%.16g", GETFLOAT(i));

    // avoid invalid UTF-8: all ASCII digits, plus period, plus, and
    // minus, are acceptable as UTF-8 characters.
    int j;
    for (j = 0; j < MAX_CHARS_FOR_DOUBLE; j++) {
        if (temp[j] != '\0' &&
            temp[j] != '.' &&
            temp[j] != '-' &&
            temp[j] != '+' &&
            !(isdigit(temp[j]))
           ) {
            fprintf(stderr, "Fatal error: invalid output from sprintf was %s!", temp);
            exit(EXIT_FAILURE);
        }
    }


    return MKSTR(vm, (utf8_byte *)temp);
}

VAL idris_castStrFloat(VM* vm, VAL i) {
    SizedString str = GETSTR(i);

    // First, we need to alloc a C string that's long enough (to get null-termination)
    char *temp = (char *) malloc(str.size + 1);
    if (temp == NULL) {
        fprintf(stderr, "Couldn't allocate temp buffer of size %lu for int->string conversion", str.size);
        exit(EXIT_FAILURE);
    }
    // Then grab the UTF8 bytes out of the Idris string. We don't have
    // to worry about nulls in the middle because we'll later check to
    // see if the whole string was used.
    memcpy(temp, str.str_data, str.size);
    temp[str.size] = '\0';

    char *end;
    double v = strtod(temp, &end);
    Closure* answer;
    // If we used the whole string, return the double, otherwise
    // return 0.0. This is the meaning of the primitive in the
    // evaluator.
    if (end == temp + str.size)
        answer = MKFLOAT(vm, v);
    else
        answer = MKFLOAT(vm, 0.0);
    free(temp);
    return answer;
}

VAL idris_concat(VM* vm, VAL l, VAL r) {
    SizedString ls = GETSTR(l);
    SizedString rs = GETSTR(r);

    Closure* cl = idris_allocate_string(rs.size + ls.size, 0);
    memcpy(cl -> info.str -> str_data, ls.str_data, ls.size);
    memcpy(cl -> info.str -> str_data + ls.size, rs.str_data, rs.size);
    assert(ISSTR(cl));
    assert(cl -> info.str -> size == ls.size + rs.size);
    return cl;
}

VAL idris_strlt(VM* vm, VAL l, VAL r) {
    SizedString ls = GETSTR(l);
    SizedString rs = GETSTR(r);

    size_t min_size = ls.size < rs.size ? ls.size : rs.size;

    //TODO: stop using strncmp to allow nulls in strings
    return MKINT((i_int)(strncmp((char *) ls.str_data,
                                 (char *) rs.str_data,
                                 min_size
                                ) < 0));
}

VAL idris_streq(VM* vm, VAL l, VAL r) {
    SizedString ls = GETSTR(l);
    SizedString rs = GETSTR(r);

    // if sizes are different, we don't need to compare contents
    if (ls.size != rs.size) {
        return MKINT(0);
    } else {
        //TODO: stop using strncmp to allow nulls in strings
        return MKINT((i_int)(strncmp((char *) ls.str_data,
                                     (char *) rs.str_data,
                                     ls.size
                                    ) == 0));
    }
}

VAL idris_strlen(VM* vm, VAL l) {
    SizedString str = GETSTR(l);
    return MKINT((i_int)(idris_utf8_strlen(str)));
}

VAL idris_readStr(VM* vm, FILE* h) {
    VAL ret;
    char *buffer = NULL;
    size_t n = 0;
    ssize_t len;
    len = getline(&buffer, &n, h);
    if (len <= 0) {
        ret = MKSTR(vm, (utf8_byte *)"");
    } else {
        // TODO: validate that buffer points to correct UTF-8
        ret = idris_allocate_string(len, 0);
        memcpy(ret -> info.str -> str_data, (utf8_byte *) buffer, len);
    }
    free(buffer);
    return ret;
}

VAL idris_strHead(VM* vm, VAL str) {
    VAL hd = idris_strIndex(vm, str, 0);
    return hd;
}

VAL MKSTROFFc(VM* vm, StrOffset* off) {
    Closure* cl = allocate(sizeof(Closure) + sizeof(StrOffset), 1);
    SETTY(cl, STROFFSET);
    cl->info.str_offset = (StrOffset*)((char*)cl + sizeof(Closure));

    cl->info.str_offset->str = off->str;
    cl->info.str_offset->offset = off->offset;

    return cl;
}

VAL idris_strTail(VM* vm, VAL str) {
    SizedString string = GETSTR(str);
    // Crash with a message when taking the tail of an empty string
    if (string.size < 1) {
        fprintf(stderr, "Tried to take the tail of an empty string.\n");
        exit(EXIT_FAILURE);
    } else if (space(vm, sizeof(Closure) + sizeof(StrOffset))) {
    // If there's no room, just copy the string, or we'll have a problem after
    // gc moves str
//        printf("space\n");
        Closure* cl = allocate(sizeof(Closure) + sizeof(StrOffset), 0);
        SETTY(cl, STROFFSET);
        cl->info.str_offset = (StrOffset*)((char*)cl + sizeof(Closure));

        int offset = 0;
        VAL root = str;

        while(root!=NULL && !ISSTR(root)) { // find the root, carry on.
                              // In theory, at most one step here!
            offset += root->info.str_offset->offset;
            root = root->info.str_offset->str;
        }

        cl -> info.str_offset -> str = root;
        cl -> info.str_offset -> offset = offset + idris_utf8_charlen(string);

        return cl;
    } else {
        SizedString nstr = GETSTR(str);
        unsigned int tailIdx = idris_utf8_charlen(nstr);
        assert(tailIdx <= nstr.size);
        Closure *cl = idris_allocate_string(nstr.size - tailIdx, 0);
        // Use memcpy here instead of MKSTR because MKSTR assumes
        // C-style strings, and 0 is a sensible Unicode character that
        // is not allowed in C UTF-8 strings.
        memcpy(cl -> info.str -> str_data, nstr.str_data + tailIdx, nstr.size - tailIdx);
        return cl;
    }
}

VAL idris_strCons(VM* vm, VAL x, VAL xs) {
    SizedString xstr = GETSTR(xs);
    unsigned int xval = GETINT(x);
    if ((xval < 0x80)) { // ASCII char
        Closure* cl = idris_allocate_string(1 + xstr.size, 0);
        cl -> info.str -> str_data[0] = (utf8_byte) xval;
        memcpy(cl -> info.str -> str_data + 1, xstr.str_data, xstr.size);
        return cl;
    } else { // Multi-byte char
        SizedString init = idris_utf8_fromChar(xval);
        Closure* cl = idris_allocate_string(init.size + xstr.size, 0);
        memcpy(cl -> info.str -> str_data, init.str_data, init.size);
        memcpy(cl -> info.str -> str_data + init.size, xstr.str_data, xstr.size);
        free(init.str_data);
        return cl;
    }
}

VAL idris_strIndex(VM* vm, VAL str, VAL i) {
    int j = GETINT(i);
    SizedString xstr = GETSTR(str);
    if (j < 0) {
        //TODO: replace internal \0 in strings before reporting error
        printf("Tried to take a negative index (%d) into a string (%s)", j, xstr.str_data);
        exit(EXIT_FAILURE);
    } else if (j >= (int)xstr.size) {
        //TODO: replace internal \0 in strings before reporting error
        printf("Tried to take too large of an index (%d) into a string (%s)", j, xstr.str_data);
        exit(EXIT_FAILURE);
    }
    unsigned int ch = idris_utf8_index(xstr.str_data, j);
    return MKINT((i_int)ch);
}

VAL idris_substr(VM* vm, VAL offset, VAL length, VAL str) {
    int off = GETINT(offset);
    int len = GETINT(length);
    SizedString xstr = GETSTR(str);
    Closure *newstr;
    if (off < 0) off = 0;
    if ((size_t) off >= xstr.size || len <= 0) {
        // If offset too far or no length, don't bother looking at
        // string and just return "".
        newstr = MKSTR(vm, (utf8_byte *) "");
    } else {
        utf8_byte *start = idris_utf8_advance(xstr.str_data, xstr.size, off);
        utf8_byte *end = idris_utf8_advance(start, xstr.size - (start - xstr.str_data), len);
        newstr = idris_allocate_string(end - start, 0);
        memcpy(newstr -> info.str -> str_data, start, end - start);
    }

    return newstr;
}

VAL idris_strRev(VM* vm, VAL str) {
    SizedString xstr = GETSTR(str);
    Closure* cl = idris_allocate_string(xstr.size, 0);

    idris_utf8_rev(xstr.str_data, cl->info.str->str_data, xstr.size);
    assert(cl -> info.str -> size == xstr.size);
    return cl;
}

VAL idris_systemInfo(VM* vm, VAL index) {
    int i = GETINT(index);
    switch(i) {
        case 0: // backend
            return MKSTR(vm, (utf8_byte *)"c");
        case 1:
            return MKSTR(vm, (utf8_byte *)IDRIS_TARGET_OS);
        case 2:
            return MKSTR(vm, (utf8_byte *)IDRIS_TARGET_TRIPLE);
    }
    return MKSTR(vm, (utf8_byte *) "");
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

    pthread_create(&t, &attr, runThread, td);
//    usleep(100);
    return vm;
}

// VM is assumed to be a different vm from the one x lives on

VAL doCopyTo(VM* vm, VAL x) {
    int i, ar;
    VAL* argptr;
    Closure* cl;
    if (x==NULL || ISINT(x)) {
        return x;
    }
    switch(GETTY(x)) {
    case CON:
        ar = CARITY(x);
        if (ar == 0 && CTAG(x) < 256) { // globally allocated
            cl = x;
        } else {
            allocCon(cl, vm, CTAG(x), ar, 1);

            argptr = (VAL*)(cl->info.c.args);
            for(i = 0; i < ar; ++i) {
                *argptr = doCopyTo(vm, *((VAL*)(x->info.c.args)+i)); // recursive version
                argptr++;
            }
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
    case MANAGEDPTR:
        cl = MKMPTRc(vm, x->info.mptr->data, x->info.mptr->size);
        break;
    case BITS8:
        cl = idris_b8CopyForGC(vm, x);
        break;
    case BITS16:
        cl = idris_b16CopyForGC(vm, x);
        break;
    case BITS32:
        cl = idris_b32CopyForGC(vm, x);
        break;
    case BITS64:
        cl = idris_b64CopyForGC(vm, x);
        break;
    case RAWDATA:
        {
            size_t size = x->info.size + sizeof(Closure);
            cl = allocate(size, 0);
            memcpy(cl, x, size);
        }
        break;
    default:
        assert(0); // We're in trouble if this happens...
    }
    return cl;
}

VAL copyTo(VM* vm, VAL x) {
    VM* current = pthread_getspecific(vm_key);
    pthread_setspecific(vm_key, vm);
    VAL ret = doCopyTo(vm, x);
    pthread_setspecific(vm_key, current);
    return ret;
}

// Add a message to another VM's message queue
int idris_sendMessage(VM* sender, VM* dest, VAL msg) {
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
    dest->inbox_write->sender = sender;
    dest->inbox_write++;

    // Wake up the other thread
    pthread_mutex_lock(&dest->inbox_block);
    pthread_cond_signal(&dest->inbox_waiting);
    pthread_mutex_unlock(&dest->inbox_block);

//    printf("Sending [signalled]...\n");

    pthread_mutex_unlock(&(dest->inbox_lock));
//    printf("Sending [unlock]...\n");
    return 1;
}

VM* idris_checkMessages(VM* vm) {
    return idris_checkMessagesFrom(vm, NULL);
}

VM* idris_checkMessagesFrom(VM* vm, VM* sender) {
    Msg* msg;

    for (msg = vm->inbox; msg < vm->inbox_end && msg->msg != NULL; ++msg) {
        if (sender == NULL || msg->sender == sender) {
            return msg->sender;
        }
    }
    return 0;
}

VM* idris_checkMessagesTimeout(VM* vm, int delay) {
    VM* sender = idris_checkMessagesFrom(vm, NULL);
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

    return idris_checkMessagesFrom(vm, NULL);
}


Msg* idris_getMessageFrom(VM* vm, VM* sender) {
    Msg* msg;
    
    for (msg = vm->inbox; msg < vm->inbox_write; ++msg) {
        if (sender == NULL || msg->sender == sender) {
            return msg;
        }
    }
    return NULL;
}

// block until there is a message in the queue
Msg* idris_recvMessage(VM* vm) {
    return idris_recvMessageFrom(vm, NULL);
}

Msg* idris_recvMessageFrom(VM* vm, VM* sender) {
    Msg* msg;
    Msg* ret = malloc(sizeof(Msg));

    struct timespec timeout;
    int status;

    pthread_mutex_lock(&vm->inbox_block);
    msg = idris_getMessageFrom(vm, sender);

    while (msg == NULL) {
//        printf("No message yet\n");
//        printf("Waiting [lock]...\n");
        timeout.tv_sec = time (NULL) + 3;
        timeout.tv_nsec = 0;
        status = pthread_cond_timedwait(&vm->inbox_waiting, &vm->inbox_block,
                               &timeout);
        (void)(status); //don't emit 'unused' warning
//        printf("Waiting [unlock]... %d\n", status);
        msg = idris_getMessageFrom(vm, sender);
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
            if (msg + 1 != vm->inbox_end) {
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

void idris_freeMsg(Msg* msg) {
    free(msg);
}

VAL* nullary_cons;

void init_nullaries() {
    int i;
    VAL cl;
    nullary_cons = malloc(256 * sizeof(VAL));
    for(i = 0; i < 256; ++i) {
        cl = malloc(sizeof(Closure));
        SETTY(cl, CON);
        cl->info.c.tag_arity = i << 8;
        nullary_cons[i] = cl;
    }
}

void free_nullaries() {
    int i;
    for(i = 0; i < 256; ++i) {
        free(nullary_cons[i]);
    }
    free(nullary_cons);
}

int __idris_argc;
char **__idris_argv;

int idris_numArgs() {
    return __idris_argc;
}

const char* idris_getArg(int i) {
    return __idris_argv[i];
}

void stackOverflow() {
  fprintf(stderr, "Stack overflow");
  exit(-1);
}
