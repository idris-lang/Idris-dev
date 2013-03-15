#ifndef _IDRIS_STATS_H
#define _IDRIS_STATS_H

#include <time.h>

// Should not be defined in release.
#define IDRIS_ENABLE_STATS

// TODO: measure user time, exclusive/inclusive stats
typedef struct {
#ifdef IDRIS_ENABLE_STATS
    int allocations;       // Size of allocated space in bytes for all execution time.
    int alloc_count;       // How many times alloc is called.
    int copied;            // Size of space copied during GC.
    int max_heap_size;     // Maximum heap size achieved.

    clock_t init_time;     // Time spent for vm initialization.
    clock_t exit_time;     // Time spent for vm termination.
    clock_t gc_time;       // Time spent for gc for all execution time.
    clock_t max_gc_pause;  // Time spent for longest gc.
    clock_t start_time;    // Time of rts entry point.
#endif // IDRIS_ENABLE_STATS
    int collections;       // How many times gc called.
} Stats; // without start time it's a monoid, can we remove start_time it somehow?

void print_stats(const Stats * stats);
void aggregate_stats(Stats * stats1, const Stats * stats2);


#ifdef IDRIS_ENABLE_STATS

#ifndef MAX
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#endif

#define STATS_INIT_STATS(stats)                 \
    memset(&stats, 0, sizeof(Stats));           \
    stats.start_time  = clock();                

#define STATS_ALLOC(stats, size)                \
    stats.allocations += size;                  \
    stats.alloc_count = stats.alloc_count + 1;

#define STATS_ENTER_INIT(stats) clock_t _start_time = clock();
#define STATS_LEAVE_INIT(stats) stats.init_time = clock() - _start_time;

#define STATS_ENTER_EXIT(stats) clock_t _start_time = clock();
#define STATS_LEAVE_EXIT(stats) stats.exit_time = clock() - _start_time;

#define STATS_ENTER_GC(stats, heap_size)                        \
    clock_t _start_time = clock();                              \
    stats.max_heap_size = MAX(stats.max_heap_size, heap_size);
#define STATS_LEAVE_GC(stats, heap_size, heap_occuped)          \
    clock_t _pause = clock() - _start_time;                     \
    stats.gc_time += _pause;                                    \
    stats.max_gc_pause = MAX(_pause, stats.max_gc_pause);       \
    stats.max_heap_size = MAX(stats.max_heap_size, heap_size);  \
    stats.copied     += heap_occuped;                           \
    stats.collections = stats.collections + 1;

#else
#define STATS_INIT_STATS(stats) memset(&stats, 0, sizeof(Stats));
#define STATS_ENTER_INIT(stats) 
#define STATS_LEAVE_INIT(stats) 
#define STATS_ENTER_EXIT(stats)
#define STATS_LEAVE_EXIT(stats)
#define STATS_ALLOC(stats, size)
#define STATS_ENTER_GC(stats, heap_size)
#define STATS_LEAVE_GC(stats, heap_size, heap_occuped)  \
    stats.collections = stats.collections + 1;
#endif // IDRIS_ENABLE_STATS

#endif // _IDRIS_STATS_H
