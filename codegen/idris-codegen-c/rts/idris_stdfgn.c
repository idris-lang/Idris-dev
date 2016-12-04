#include "idris_stdfgn.h"
#include "idris_rts.h"
#include "idris_gmp.h"
#include "idris_gc.h"

#include <fcntl.h>
#include <errno.h>
#include <sys/stat.h>
#include <stdio.h>
#include <time.h>

#if defined(WIN32) || defined(__WIN32) || defined(__WIN32__)
int win_fpoll(void* h);
#else
#include <sys/select.h>
#endif

extern char** environ;

void putStr(char* str) {
    printf("%s", str);
}

void* fileOpen(char* name, char* mode) {
    FILE* f = fopen(name, mode);
    return (void*)f;
}

void fileClose(void* h) {
    FILE* f = (FILE*)h;
    fclose(f);
}

int fileEOF(void* h) {
    FILE* f = (FILE*)h;
    return feof(f);
}

int fileError(void* h) {
    FILE* f = (FILE*)h;
    return ferror(f);
}

int fileSize(void* h) {
    FILE* f = (FILE*)h;
    int fd = fileno(f);

    struct stat buf;
    if (fstat(fd, &buf) == 0) {
        return (int)(buf.st_size);
    } else {
        return -1;
    }
}

int idris_writeStr(void* h, char* str) {
    FILE* f = (FILE*)h;
    if (fputs(str, f)) {
        return 0;
    } else {
        return -1;
    }
}

int fpoll(void* h)
{
#if defined(WIN32) || defined(__WIN32) || defined(__WIN32__)
    return win_fpoll(h);
#else
    FILE* f = (FILE*)h;
    fd_set x;
    struct timeval timeout;
    timeout.tv_sec = 1;
    timeout.tv_usec = 0;
    int fd = fileno(f);

    FD_ZERO(&x);
    FD_SET(fd, &x);

    int r = select(fd+1, &x, 0, 0, &timeout);
    return r;
#endif
}

void* do_popen(const char* cmd, const char* mode) {
    FILE* f = popen(cmd, mode);
//    int d = fileno(f);
//    fcntl(d, F_SETFL, O_NONBLOCK);
    return f;
}

int isNull(void* ptr) {
    return ptr==NULL;
}

int idris_eqPtr(void* x, void* y) {
    return x==y;
}

void* idris_stdin() {
    return (void*)stdin;
}

char* getEnvPair(int i) {
    return *(environ + i);
}

VAL idris_time() {
    time_t t = time(NULL);
    return MKBIGI(t);
}

VAL idris_mkFileError(VM* vm) {
    VAL result;
    switch(errno) {
        // Make sure this corresponds to the FileError structure in
        // Prelude.File
        case ENOENT:
            idris_constructor(result, vm, 3, 0, 0);
            break;
        case EACCES:
            idris_constructor(result, vm, 4, 0, 0);
            break;
        default:
            idris_constructor(result, vm, 0, 1, 0);
            idris_setConArg(result, 0, MKINT((intptr_t)errno));
            break;
    }
    return result;
}

void idris_forceGC(void* vm) {
    idris_gc((VM*)vm);
}
