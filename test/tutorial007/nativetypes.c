#include <stdio.h>

int sizeof_size_t() {
  int sz = sizeof(size_t);

  FILE *f = fopen("sizefromc.txt", "w");
  if (f == NULL) {
    printf("Failed to open file from C");
  }
  fprintf(f, "%d bytes", sz);

  return sz;
}
