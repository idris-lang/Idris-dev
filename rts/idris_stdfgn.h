#ifndef _IDRISSTDFGN_H
#define _IDRISSTDFGN_H

// A collection of useful standard functions to be used by the prelude.

void putStr(char* str);
//char* readStr();

void* fileOpen(char* f, char* mode);
void fileClose(void* h);
char* freadStr(void* h);
void fputStr(void*h, char* str);

int isNull(void* ptr);
void* idris_stdin();

#endif
