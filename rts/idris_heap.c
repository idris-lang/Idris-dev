#include "idris_heap.h"
#include "idris_rts.h"

#include <stdlib.h>
#include <stddef.h>
#include <stdio.h>

void alloc_heap(Heap * h, size_t heap_size) 
{
    char * mem = malloc(heap_size); 
    if (mem == NULL) {
        fprintf(stderr, 
                "RTS ERROR: Unable to allocate heap. Requested %d bytes.\n",
                (int)heap_size);
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

// TODO: more testing
/******************** Heap testing ********************************************/
void heap_check_underflow(Heap * heap) {
    if (!(heap->heap <= heap->next)) {
       fprintf(stderr, "RTS ERROR: HEAP UNDERFLOW <bot %p> <cur %p>\n", 
               heap->heap, heap->next);
        exit(EXIT_FAILURE);
    }
}

void heap_check_overflow(Heap * heap) {
    if (!(heap->next <= heap->end)) {
       fprintf(stderr, "RTS ERROR: HEAP OVERFLOW <cur %p> <end %p>\n", 
               heap->next, heap->end);
        exit(EXIT_FAILURE);
    }
}

int is_valid_ref(VAL v) {
    return (v != NULL) && !(ISINT(v));
}

int ref_in_heap(Heap * heap, VAL v) { 
    return ((VAL)heap->heap <= v) && (v < (VAL)heap->next);
}

// Checks three important properties:
// 1. Closure.
//      Check if all pointers in the _heap_ points only to heap. 
// 2. Unidirectionality. (if compact gc)
//      All references in the heap should be are unidirectional. In other words,
//      more recently allocated closure can point only to earlier allocated one.
// 3. After gc there should be no forward references.
//
void heap_check_pointers(Heap * heap) {
    char* scan = NULL;
  
    size_t item_size = 0;
    for(scan = heap->heap; scan < heap->next; scan += item_size) {
       item_size = *((size_t*)scan);
       VAL heap_item = (VAL)(scan + sizeof(size_t));

       switch(GETTY(heap_item)) {
       case CON:
           {
             int ar = ARITY(heap_item);
             int i = 0;
             for(i = 0; i < ar; ++i) {
                 VAL ptr = heap_item->info.c.args[i];

                 if (is_valid_ref(ptr)) {
                     // Check for closure.
                     if (!ref_in_heap(heap, ptr)) {
                         fprintf(stderr, 
                                 "RTS ERROR: heap closure broken. "\
                                 "<HEAP %p %p %p> <REF %p>\n",
                                 heap->heap, heap->next, heap->end, ptr);
                         exit(EXIT_FAILURE);
                     }
#if 0 // TODO macro
                     // Check for unidirectionality.
                     if (!(ptr < heap_item)) {
                         fprintf(stderr, 
                                 "RTS ERROR: heap unidirectionality broken:" \
                                 "<CON %p> <FIELD %p>\n",
                                 heap_item, ptr);
                         exit(EXIT_FAILURE);
                     }
#endif
                 }
             }
             break;
           }
       case BUFOFFSET:
           if (!ref_in_heap(heap, heap_item->info.buf_offset->buf)) {
               fprintf(stderr,
                       "RTS ERROR: heap closure broken. "\
                       "<HEAP %p %p %p> <REF %p>\n",
                       heap->heap, heap->next, heap->end, heap_item->info.buf_offset->buf);
               exit(EXIT_FAILURE);
           }
           break;
       case FWD:
           // Check for artifacts after cheney gc.
           fprintf(stderr, "RTS ERROR: FWD in working heap.\n");
           exit(EXIT_FAILURE);
           break;
       default:
           break;
       }
    }
}

void heap_check_all(Heap * heap)
{
    heap_check_underflow(heap);
    heap_check_overflow(heap);
    heap_check_pointers(heap);
}
