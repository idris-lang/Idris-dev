#ifndef _THREADS_H
#define _THREADS_H

int idris_newLock();
void idris_doLock(int lock);
void idris_doUnlock(int lock);
void idris_doFork(void* proc);
void* idris_doWithin(int limit, void* proc, void* doOnFail);
int idris_utime();

#endif
