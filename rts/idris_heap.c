#include "idris_heap.h"

#include <stdlib.h>
#include <stddef.h>
#include <stdio.h>

void alloc_heap(Heap * h, size_t heap_size) 
{
    char * mem = malloc(heap_size); 
    if (mem == NULL) {
        fprintf(stderr, "Unable to allocate heap. Requested %d bytes.\n", heap_size);
        exit(EXIT_FAILURE);
    }

    h->heap = mem;
    h->next = h->heap;
    h->end  = h->heap + heap_size;

    h->size   = heap_size;
    h->growth = heap_size;

    h->old = NULL;
}

void free_heap(Heap * h) {
    free(h->heap);

    if (h->old != NULL) { 
        free(h->old); 
    }
}
