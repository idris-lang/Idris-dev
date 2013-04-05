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

char* freadStr(void* h) {
  FILE* f = (FILE*)h;
  char* str;
  printf("foo");
  if (f != NULL) {
    fseek(f, 0L, SEEK_END);
    size_t size = ftell(f);
    rewind(f);
    printf("bar");
    str = malloc(size + sizeof(char));
    if (str != NULL && fread(str, size, 1, f)) {
      (*(str + size)) = '\0';
      printf("asf");
    } else {
      printf("Failed to allocate string from file\n");
      exit(1);
    }
  } else {
    str = malloc(sizeof(char));
    str[0] = '\0';
  }
  return str;
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
