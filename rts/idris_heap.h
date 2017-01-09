#ifndef _IDRIS_HEAP_H
#define _IDRIS_HEAP_H

#include <stdbool.h>
#include <stddef.h>

/* *** C heap ***
 * Objects with finalizers. Mark&sweep-collected.
 *
 * The C heap is implemented as a doubly linked list
 * of pointers coupled with their finalizers.
 */

struct VM;

#define C_HEAP_GC_TRIGGER_SIZE(heap_size) \
    (heap_size < 2048    \
        ? 4096           \
        : 2 * heap_size  \
    )

typedef void CDataFinalizer(void *);

typedef struct CHeapItem {
    /// Payload.
    void * data;

    /// Size of the item, in bytes.
    /// This does not have to be a precise size. It is used to assess
    /// whether the heap needs garbage collection.
    size_t size;

    /// Finalizer that will be called on the payload pointer.
    /// Its job is to deallocate all associated resources,
    /// including the memory pointed to by `data` (if any).
    CDataFinalizer * finalizer;

    /// The mark bit set by the FP heap traversal,
    /// cleared by C heap sweep.
    bool is_used;

    /// Next item in the C heap.
    struct CHeapItem * next;

    /// Pointer to the previous next-pointer.
    struct CHeapItem ** prev_next;
} CHeapItem;

typedef struct CHeap {
    /// The first item in the heap. NULL if the heap is empty.
    CHeapItem * first;

    /// Total size of the heap. (Sum of sizes of items.)
    /// This may not be a precise size since individual items'
    /// sizes may be just estimates.
    size_t size;

    /// When heap reaches this size, GC will be triggered.
    size_t gc_trigger_size;
} CHeap;

/// Create a C heap.
void c_heap_init(CHeap * c_heap);

/// Destroy the given C heap. Will not deallocate the given pointer.
/// Will call finalizers & deallocate all blocks in the heap.
void c_heap_destroy(CHeap * c_heap);

/// Insert the given item into the heap if it's not there yet.
/// The VM pointer is needed because this operation may trigger GC.
void c_heap_insert_if_needed(struct VM * vm, CHeap * c_heap, CHeapItem * item);

/// Mark the given item as used.
void c_heap_mark_item(CHeapItem * item);

/// Sweep the C heap, finalizing and freeing unused blocks.
void c_heap_sweep(CHeap * c_heap);

/// Create a C heap item from its payload, size estimate, and finalizer.
/// The size does not have to be precise but it should roughly reflect
/// how big the item is for GC to work effectively.
CHeapItem * c_heap_create_item(void * data, size_t size, CDataFinalizer * finalizer);

/* *** Idris heap **
 * Objects without finalizers. Cheney-collected.
 */

typedef struct {
    char*  next;   // Next allocated chunk. Should always (heap <= next < end).
    char*  heap;   // Point to bottom of heap
    char*  end;    // Point to top of heap
    size_t size;   // Size of _next_ heap. Size of current heap is /end - heap/.
    size_t growth; // Quantity of heap growth in bytes.

    char* old;
} Heap;


void alloc_heap(Heap * heap, size_t heap_size, size_t growth, char * old);
void free_heap(Heap * heap);
char* aligned_heap_pointer(char * heap);

#ifdef IDRIS_DEBUG
void heap_check_all(Heap * heap);
// Should be used _between_ gc's.
#define HEAP_CHECK(vm) heap_check_all(&(vm->heap));
#else
#define HEAP_CHECK(vm)
#endif // IDRIS_DEBUG

#endif // _IDRIS_HEAP_H
