#include <closure.h>
#include "threads.h"

// Threads and locks

typedef struct {
    pthread_mutex_t m_id;
} Mutex;

typedef struct {
    pthread_t t_id;
} Thread;

Mutex** ms = NULL;
int mutexes = 0;

int idris_newLock(int sem)
{
    pthread_mutex_t m;

    pthread_mutex_init(&m, NULL);
    Mutex* newm = EMALLOC(sizeof(Mutex));
    newm->m_id = m;

    // Increase space for the mutexes
    if (ms==NULL) {
	ms = (Mutex**)EMALLOC(sizeof(Mutex*));
	mutexes=1;
    } else {
	ms = (Mutex**)(EREALLOC(ms, sizeof(Mutex*)*(mutexes+1)));
	mutexes++;
    }

    ms[mutexes-1] = newm;
    return mutexes-1;
}

void idris_doLock(int lock)
{
    pthread_mutex_lock(&(ms[lock]->m_id));
}

void idris_doUnlock(int lock)
{
    pthread_mutex_unlock(&(ms[lock]->m_id));
}

struct threadinfo {
    void* proc;
    void* result;
};

void* idris_runThread(void* th_in) {
    struct threadinfo* th = (struct threadinfo*)th_in;
    void* v = DO_EVAL(th->proc, 1);
    th->result = v;
    return v;
}

void idris_doFork(void* proc)
{
    pthread_t* t = EMALLOC(sizeof(pthread_t));
    struct threadinfo th;
    th.proc = proc;
    th.result = NULL;
    pthread_create(t, NULL, idris_runThread, &th);
}

void* idris_doWithin(int limit, void* proc, void* doOnFail)
{
    pthread_t* t = EMALLOC(sizeof(pthread_t));
//    printf("CREATING THREAD %d\n", t);
    struct threadinfo th;
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
