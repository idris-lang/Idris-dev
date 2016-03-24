#include <stdint.h>
typedef int (*callback)(int);

int32_t testvar = 887;

void test_ffi(int (*cb)(int));

void test_ffi2(int (*cb)(char*));
void test_ffi3(void (*cb)(void));

callback test_ffi6(void);

void test_mulpar(void (*fn)(int, int));
