#pragma once

#include <stdint.h>
#include <stddef.h>

#include "idris_rts.h"


CData array_alloc(int size);
void array_realloc(int size, CData array);
uint8_t array_peek(int ofs, CData array);
int array_peek_int(int ofs, CData array);
void array_poke(int ofs, uint8_t byte, CData array);
void array_poke_int(int ofs, int i, CData array);
void array_copy(CData src, int src_ofs, CData dst, int dst_ofs, int count);
void array_fill(int ofs, int count, uint8_t byte, CData array);
int array_compare(CData l, int lofs, CData r, int rofs, int count);
int array_find(uint8_t byte, CData array, int ofs, int end);
