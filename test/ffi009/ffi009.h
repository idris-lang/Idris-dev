#ifndef FFI009_H
#define FFI009_H

#include <idris_rts.h>


typedef struct
{
  unsigned char* value;
  int length;
} Vect;

int get_allocation_size(Vect* v);

Vect* new_empty_vect(int length);

Vect* foo(int length);
Vect* bar(int length);

#endif /* FFI009_H */
