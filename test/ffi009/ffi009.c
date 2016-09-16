#include "ffi009.h"


Vect* foo(int length)
{
  return new_empty_vect(length);
}

Vect* bar(int length)
{
  return new_empty_vect(length * 2);
}


Vect* new_empty_vect(int l)
{
  unsigned char* vect;

  vect = malloc(sizeof(unsigned char) * l);

  if (vect == NULL){
    free(vect);
    return NULL;
  }

  Vect* v = malloc(sizeof(Vect));

  if (v==NULL){
    free(vect);
    free(v);
    return NULL;
  }

  v->value  = vect;
  v->length = l;

  return v;
}


int get_allocation_size(Vect* v)
{
  return sizeof(Vect) + v->length;
}
