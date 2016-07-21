#include "sys.h"

#include <stdlib.h>

int WIFEXITED_(int status) {
  return WIFEXITED(status);
}

int WEXITSTATUS_(int status) {
  return WEXITSTATUS(status);
}
