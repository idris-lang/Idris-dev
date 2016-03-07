#include "ffi008.h"
#include <stdio.h>

int size1(void) {
    return sizeof(struct test1);
}

int size2(void) {
    return sizeof(struct test2);
}

void print_mystruct(void) {
    printf("a: %d b: %d\n", mystruct.a, mystruct.b);
}
