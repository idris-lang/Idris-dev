#ifndef _IDRIS_OPTS_H
#define _IDRIS_OPTS_H

#include <stddef.h>
#include <stdio.h>

typedef struct {
    size_t init_heap_size;
    size_t max_stack_size;
    int    show_summary;
} RTSOpts;

void print_usage(FILE * s);

// Parse rts options and shift arguments such that rts options becomes invisible
// for main program.
void parse_shift_args(RTSOpts * opts, int * argc, char *** argv);

#endif
