#include <stdint.h>

struct test1 {
    int8_t a;
    int64_t b;
};

struct test2 {
    int32_t a;
    int16_t b;
};

struct test2 mystruct;

int size1(void);
int size2(void);
void print_mystruct();
