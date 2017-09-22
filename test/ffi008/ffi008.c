#include <stdio.h>
#include <stdlib.h>

#include "ffi008.h"

int size1(void) {
    return sizeof(struct test1);
}

int size2(void) {
    return sizeof(struct test2);
}

void print_mystruct(void) {
    printf("a: %d b: %d\n", mystruct.a, mystruct.b);
}

struct test2* calc_struct(struct test1 *in)
{
    struct test2 *out = malloc(sizeof(struct test2));
    out->a = in->a * in->a;
    out->b = in->b & 0x0000FFFF;

    return out;
}
