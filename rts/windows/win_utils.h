#include <stdint.h>
#include <stdio.h>

#pragma once

int win_fpoll(void *h);
FILE *win32_u8fopen(const char *path, const char *mode);
FILE *win32_u8popen(const char *path, const char *mode);
void win32_gettime(int64_t* sec, int64_t* nsec);
