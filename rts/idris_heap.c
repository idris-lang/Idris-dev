#include "idris_heap.h"
#include "idris_rts.h"
#include "idris_gc.h"

#include <stdlib.h>
#include <stddef.h>
#include <stdio.h>
#include <assert.h>

static void c_heap_free_item(CHeap * heap, CHeapItem * item)
{
    assert(item->size <= heap->size);
    heap->size -= item->size;

    // fix links
    if (item->next != NULL)
    {
        item->next->prev_next = item->prev_next;
    }
    *(item->prev_next) = item->next;

    // free payload
    item->finalizer(item->data);

    // free item struct
    free(item);
}

CHeapItem * c_heap_create_item(void * data, size_t size, CDataFinalizer * finalizer)
{
    CHeapItem * item = (CHeapItem *) malloc(sizeof(CHeapItem));

    item->data = data;
    item->size = size;
    item->finalizer = finalizer;
    item->is_used = false;
    item->next = NULL;
    item->prev_next = NULL;

    return item;
}

void c_heap_insert_if_needed(VM * vm, CHeap * heap, CHeapItem * item)
{
    if (item->prev_next != NULL) return;  // already inserted

    if (heap->first != NULL)
    {
        heap->first->prev_next = &item->next;
    }

    item->prev_next = &heap->first;
    item->next = heap->first;

    heap->first = item;

    // at this point, links are done; let's calculate sizes
    
    heap->size += item->size;
    if (heap->size >= heap->gc_trigger_size)
    {
        item->is_used = true;  // don't collect what we're inserting
        idris_gc(vm);
    }
}

void c_heap_mark_item(CHeapItem * item)
{
    item->is_used = true;
}

void c_heap_sweep(CHeap * heap)
{
    CHeapItem * p = heap->first;
    while (p != NULL)
    {
        if (p->is_used)
        {
            p->is_used = false;
            p = p->next;
        }
        else
        {
            CHeapItem * unused_item = p;
            p = p->next;

            c_heap_free_item(heap, unused_item);
        }
    }

    heap->gc_trigger_size = C_HEAP_GC_TRIGGER_SIZE(heap->size);
}

void c_heap_init(CHeap * heap)
{
    heap->first = NULL;
    heap->size = 0;
    heap->gc_trigger_size = C_HEAP_GC_TRIGGER_SIZE(heap->size);
}

void c_heap_destroy(CHeap * heap)
{
    while (heap->first != NULL)
    {
        c_heap_free_item(heap, heap->first);  // will update heap->first via the backward link
    }
}

/* Used for initializing the FP heap. */
void alloc_heap(Heap * h, size_t heap_size, size_t growth, char * old)
{
    char * mem = malloc(heap_size);
    if (mem == NULL) {
        fprintf(stderr,
                "RTS ERROR: Unable to allocate heap. Requested %zd bytes.\n",
                heap_size);
        exit(EXIT_FAILURE);
    }

    h->heap = mem;
    h->next = aligned_heap_pointer(h->heap);
    h->end  = h->heap + heap_size;

    h->size   = heap_size;
    h->growth = growth;

    h->old = old;
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

char* aligned_heap_pointer(char * heap) {
#ifdef FORCE_ALIGNMENT
    if (((i_int)heap&1) == 1) {
	    return (heap + 1);
    } else
#endif
    {
	    return heap;
    }
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
       case CT_CON:
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
                                 "<CT_CON %p> <FIELD %p>\n",
                                 heap_item, ptr);
                         exit(EXIT_FAILURE);
                     }
#endif
                 }
             }
             break;
           }
       case CT_FWD:
           // Check for artifacts after cheney gc.
           fprintf(stderr, "RTS ERROR: CT_FWD in working heap.\n");
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
