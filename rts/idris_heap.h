#ifndef _IDRIS_HEAP_H
#define _IDRIS_HEAP_H

#include <stddef.h>

typedef struct {
    char*  next;   // Next allocated chunk. Should always (heap <= next < end).
    char*  heap;   // Point to bottom of heap
    char*  end;    // Point to top of heap
    size_t size;   // Size of _next_ heap. Size of current heap is /end - heap/.
    size_t growth; // Quantity of heap growth in bytes. TODO: should it be constant?

    char* old;
    // TODO heap usage
} Heap;


void alloc_heap(Heap * heap, size_t heap_size);
void free_heap(Heap * heap);


#ifdef IDRIS_DEBUG
void heap_check_all(Heap * heap);
// Should be used _between_ gc's.
#define HEAP_CHECK(vm) heap_check_all(&(vm->heap));
#else
#define HEAP_CHECK(vm) 
#endif // IDRIS_DEBUG

#endif // _IDRIS_HEAP_H
