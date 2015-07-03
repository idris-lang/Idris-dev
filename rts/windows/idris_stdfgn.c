#include "../idris_stdfgn.h"
#include "../idris_rts.h"
#include "../idris_gc.h"

#include <fcntl.h>
#include <stdio.h>
#include <time.h>
#include <io.h>

extern char** environ;

int win_fpoll(void* h);

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
    return win_fpoll(h);
}

void* do_popen(const char* cmd, const char* mode) {
    FILE* f = _popen(cmd, mode);
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

void idris_forceGC(void* vm) {
   idris_gc((VM*)vm);
}
