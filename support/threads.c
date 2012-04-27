#include <closure.h>
#include "threads.h"

// Threads and locks

typedef struct {
    pthread_mutex_t m_id;
} IdrisMutex;

typedef struct {
    pthread_t t_id;
} IdrisThread;

IdrisMutex** idris_ms = NULL;
int idris_mutexes = 0;

int idris_newLock()
{
    pthread_mutex_t m;

    pthread_mutex_init(&m, NULL);
    IdrisMutex* newm = EMALLOC(sizeof(IdrisMutex));
    newm->m_id = m;

    // Increase space for the mutexes
    if (idris_ms==NULL) {
	idris_ms = (IdrisMutex**)EMALLOC(sizeof(IdrisMutex*));
	idris_mutexes=1;
    } else {
	idris_ms = (IdrisMutex**)(EREALLOC(idris_ms, sizeof(IdrisMutex*)*(idris_mutexes+1)));
	idris_mutexes++;
    }

    idris_ms[idris_mutexes-1] = newm;
    return idris_mutexes-1;
}

void idris_doLock(int lock)
{
    pthread_mutex_lock(&(idris_ms[lock]->m_id));
}

void idris_doUnlock(int lock)
{
    pthread_mutex_unlock(&(idris_ms[lock]->m_id));
}

struct idris_threadinfo {
    void* proc;
    void* result;
};

void* idris_runThread(void* th_in) {
    printf("IN THREAD\n");
    struct idris_threadinfo* th = (struct idris_threadinfo*)th_in;
    printf("using %d\n", th_in);
    void* v = DO_EVAL(th_in, 1);
    th->result = v;
    return v;
}

void idris_doFork(void* proc)
{
    printf("FORKING!\n");
    pthread_t* t = malloc(sizeof(pthread_t));
    struct idris_threadinfo th;
    printf("in %d\n", proc);
    th.proc = proc;
    th.result = NULL;
    pthread_create(t, NULL, idris_runThread, proc);
    printf("FORKED!\n");
}

void* idris_doWithin(int limit, void* proc, void* doOnFail)
{
    pthread_t* t = EMALLOC(sizeof(pthread_t));
//    printf("CREATING THREAD %d\n", t);
    struct idris_threadinfo th;
    th.proc = proc;
    th.result = NULL;

    struct timeval tv;
    gettimeofday(&tv, NULL);
    int tnow, tthen = do_utime();

    pthread_create(t, NULL, idris_runThread, &th);
//    printf("tthen %d\n", tthen);

    void* ans;

    do 
    {
	// If the answer has been updated, we're done.
	if (th.result!=NULL) {
	    pthread_join(*t, &ans);
	    return ans;
	}
	gettimeofday(&tv, NULL);
	tnow = idris_utime();
	usleep(100);
//	printf("tnow %d\n", tnow);
    }
    while(tnow<(tthen+(limit*1000)));
    pthread_cancel(*t);
    return DO_EVAL(doOnFail,1);
}

int idris_utime() {
    struct timeval tv;
    gettimeofday(&tv, NULL);

    static int start=0;
    if (start==0) { start = tv.tv_sec; }

    return 1000000*(tv.tv_sec - start)+tv.tv_usec;
}
