#ifndef _IDRISSTDFGN_H
#define _IDRISSTDFGN_H

#include "idris_rts.h"

// A collection of useful standard functions to be used by the prelude.

void putStr(char* str);
//char* readStr();

void* fileOpen(char* f, char* mode);
void fileClose(void* h);
int fileEOF(void* h);
int fileError(void* h);
// Returns a negative number if not a file (e.g. directory or device)
int fileSize(void* h);

// Return a negative number if not a file (e.g. directory or device)
VAL fileAccessTime(void* h);
VAL fileModifiedTime(void* h);
VAL fileStatusTime(void* h);

void* idris_dirOpen(char* dname);
void idris_dirClose(void* h);
char* idris_nextDirEntry(void* h);

// Create a directory; return 0 on success or -1 on failure
int idris_mkdir(char* dname);
int idris_chdir(char* dname);

// Return 0 if ok, or -1 if there was an error with the given directory
// (like ferror)
int idris_dirError(void *dptr);

// return 0 on success
int idris_writeStr(void*h, char* str);
// construct a file error structure (see Prelude.File) from errno
VAL idris_mkFileError(VM* vm);

// Some machinery for building a large string without reallocating
// Create a string with space for 'len' bytes
void* idris_makeStringBuffer(int len);
void idris_addToString(void* buffer, char* str);
VAL idris_getString(VM* vm, void* buffer);

void* do_popen(const char* cmd, const char* mode);
int fpoll(void* h);

int isNull(void* ptr);
void* idris_stdin();

char* getEnvPair(int i);

VAL idris_time();

void idris_forceGC();

VAL idris_currentDir();

#endif
