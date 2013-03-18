#include "idris_stats.h"

#include <stdio.h>
#include <locale.h>

#ifdef IDRIS_ENABLE_STATS

void print_stats(const Stats * stats) {
    clock_t total   = clock() - stats->start_time;
    clock_t mut     = total - stats->init_time - stats->gc_time - stats->exit_time;
    double  mut_sec = (double)mut   / CLOCKS_PER_SEC;

    int avg_chunk = 0;
    if (stats->alloc_count > 0) {
        avg_chunk = (int)((double)stats->allocations / (double)stats->alloc_count);
    }

    int alloc_rate = 0;
    if (mut > 0) {
        alloc_rate  = (int)((double)(stats->allocations) / mut_sec);
    }
    
    double gc_percent = 0.0d;
    double productivity = 0.0d;
    if (total > 0) {
        gc_percent = 100 * (double)stats->gc_time / (double)total;
        productivity = 100 * ((double)mut / (double)total);
    }

    setlocale(LC_NUMERIC, "");
    printf("\n");
    printf("%'20d bytes allocated in the heap\n",  stats->allocations);
    printf("%'20d bytes copied during GC\n",       stats->copied);
    printf("%'20d maximum heap size\n",            stats->max_heap_size);
    printf("%'20d chunks allocated in the heap\n", stats->alloc_count);
    printf("%'20d average chunk size\n\n",         avg_chunk);

    printf("GC called %d times\n\n", stats->collections);

    printf("INIT  time: %8.3fs\n",   (double)stats->init_time / CLOCKS_PER_SEC);
    printf("MUT   time: %8.3fs\n",   mut_sec);
    printf("GC    time: %8.3fs\n",   (double)stats->gc_time   / CLOCKS_PER_SEC);
    printf("EXIT  time: %8.3fs\n",   (double)stats->exit_time / CLOCKS_PER_SEC);
    printf("TOTAL time: %8.3fs\n\n", (double)total            / CLOCKS_PER_SEC);

    printf("%%GC   time: %.2f%%\n\n", gc_percent);

    printf("Alloc rate %'d bytes per MUT sec\n\n", alloc_rate);

    printf("Productivity %.2f%%\n", productivity);
}

void aggregate_stats(Stats * stats1, const Stats * stats2) {
    fprintf(stderr, "RTS error: aggregate_stats not implemented");
}

#else

void print_stats(const Stats * stats) {
    fprintf(stderr, "RTS ERROR: Stats are disabled.\n"  \
                    "By the way GC called %d times.\n", stats->collections);
}

void aggregate_stats(Stats * stats1, const Stats * stats2) {
    stats1->collections += stats2->collections;
}

#endif // IDRIS_ENABLE_STATS
