#include "array.h"
#include <string.h>

int array_find(uint8_t byte, CData array, int ofs, int end)
{
    void * data = array->data + ofs;
    void * result = memchr(data, (int) byte, (size_t) (end - ofs));
    if (result == NULL)
    {
        return -1;
    }
    else
    {
        return (result - data);
    }
}

void array_realloc(int size, CData array)
{
    array->data = realloc(array->data, (size_t) size);
}

CData array_alloc(int size)
{
    return cdata_allocate((size_t) size, free);
}

uint8_t array_peek(int ofs, CData array)
{
    return ((uint8_t *) array->data)[ofs];
}

void array_poke(int ofs, uint8_t byte, CData array)
{
    ((uint8_t *) array->data)[ofs] = byte;
}

int array_peek_int(int ofs, CData array)
{
    return *((int *) (array->data + ofs));
}

void array_poke_int(int ofs, int val, CData array)
{
    *((int *) (array->data + ofs)) = val;
}

void array_copy(CData src, int src_ofs, CData dst, int dst_ofs, int count)
{
    // memmove rather than memcpy in case the areas overlap
    memmove(dst->data + dst_ofs, src->data + src_ofs, count);
}

void array_fill(int ofs, int count, uint8_t byte, CData array)
{
    memset(array->data + ofs, byte, count);
}

int array_compare(CData l, int lofs, CData r, int rofs, int count)
{
    return memcmp(l->data + lofs, r->data + rofs, count);
}
