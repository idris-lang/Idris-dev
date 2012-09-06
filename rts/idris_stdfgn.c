#include "idris_stdfgn.h"
#include "idris_rts.h"

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

void fputStr(void* h, char* str) {
    FILE* f = (FILE*)h;
    fputs(str, f);
}

int isNull(void* ptr) {
    return ptr==NULL;
}

void* idris_stdin() {
    return (void*)stdin;
}

