#include "sys.h"

#include <stdlib.h>

#ifdef __OpenBSD__
#include <sys/wait.h>
#endif

int WIFEXITED_(int status) {
  return WIFEXITED(status);
}

int WEXITSTATUS_(int status) {
  return WEXITSTATUS(status);
}
