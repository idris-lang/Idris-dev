#include "test033.h"
#include <stddef.h>

int testNull(void* p) {
  if(p == NULL) {
    return 0;
  }
  return 1;
}

