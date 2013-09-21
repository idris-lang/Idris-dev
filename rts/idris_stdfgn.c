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

int fileEOF(void* h) {
  FILE* f = (FILE*)h;
  return feof(f);
}

int fileError(void* h) {
  FILE* f = (FILE*)h;
  return ferror(f);
}

void fputStr(void* h, char* str) {
    FILE* f = (FILE*)h;
    fputs(str, f);
}

int isNull(void* ptr) {
    return ptr==NULL;
}

int isNullString(char* str) {
    return str==NULL;
}

void* idris_stdin() {
    return (void*)stdin;
}
