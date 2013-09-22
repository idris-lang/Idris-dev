#include <stdlib.h>
#include <stdio.h>
#include <gmp.h>
#include <gc.h>
#include <string.h>
#include <inttypes.h>

extern char** environ;

void putStr(const char *str) {
  fputs(str, stdout);
}

void mpz_init_set_ull(mpz_t n, unsigned long long ull)
{
  mpz_init_set_ui(n, (unsigned int)(ull >> 32)); /* n = (unsigned int)(ull >> 32) */
  mpz_mul_2exp(n, n, 32);                   /* n <<= 32 */
  mpz_add_ui(n, n, (unsigned int)ull);      /* n += (unsigned int)ull */
}

void mpz_init_set_sll(mpz_t n, long long sll)
{
  mpz_init_set_si(n, (int)(sll >> 32));     /* n = (int)sll >> 32 */
  mpz_mul_2exp(n, n, 32 );             /* n <<= 32 */
  mpz_add_ui(n, n, (unsigned int)sll); /* n += (unsigned int)sll */
}

void mpz_set_sll(mpz_t n, long long sll)
{
  mpz_set_si(n, (int)(sll >> 32));     /* n = (int)sll >> 32 */
  mpz_mul_2exp(n, n, 32 );             /* n <<= 32 */
  mpz_add_ui(n, n, (unsigned int)sll); /* n += (unsigned int)sll */
}

unsigned long long mpz_get_ull(mpz_t n)
{
  unsigned int lo, hi;
  mpz_t tmp;

  mpz_init( tmp );
  mpz_mod_2exp( tmp, n, 64 );   /* tmp = (lower 64 bits of n) */

  lo = mpz_get_ui( tmp );       /* lo = tmp & 0xffffffff */ 
  mpz_div_2exp( tmp, tmp, 32 ); /* tmp >>= 32 */
  hi = mpz_get_ui( tmp );       /* hi = tmp & 0xffffffff */

  mpz_clear( tmp );

  return (((unsigned long long)hi) << 32) + lo;
}

char *__idris_strCons(char c, char *s) {
  size_t len = strlen(s);
  char *result = GC_malloc_atomic(len+2);
  result[0] = c;
  memcpy(result+1, s, len);
  result[len+1] = 0;
  return result;
}

#define BUFSIZE 256
char *__idris_readStr(FILE* h) {
// Modified from 'safe-fgets.c' in the gdb distribution.
// (see http://www.gnu.org/software/gdb/current/)
  char *line_ptr;
  char* line_buf = (char *) GC_malloc (BUFSIZE);
  int line_buf_size = BUFSIZE;

  /* points to last byte */
  line_ptr = line_buf + line_buf_size - 1;

  /* so we can see if fgets put a 0 there */
  *line_ptr = 1;
  if (fgets (line_buf, line_buf_size, h) == 0)
    return "";

  /* we filled the buffer? */
  while (line_ptr[0] == 0 && line_ptr[-1] != '\n')
  {
    /* Make the buffer bigger and read more of the line */
    line_buf_size += BUFSIZE;
    line_buf = (char *) GC_realloc (line_buf, line_buf_size);

    /* points to last byte again */
    line_ptr = line_buf + line_buf_size - 1;
    /* so we can see if fgets put a 0 there */
    *line_ptr = 1;

    if (fgets (line_buf + line_buf_size - BUFSIZE - 1, BUFSIZE + 1, h) == 0)
      return "";
  }

  return line_buf;
}

void* fileOpen(char* name, char* mode) {
  FILE* f = fopen(name, mode);
  return (void*)f;
}

void fileClose(void* h) {
  FILE* f = (FILE*)h;
  fclose(f);
}

int fileEOF(void* h) {
  FILE* f = (FILE*)h;
  return feof(f);
}

int fileError(void* h) {
  FILE* f = (FILE*)h;
  return ferror(f);
}

void fputStr(void* h, char* str) {
  FILE* f = (FILE*)h;
  fputs(str, f);
}

int isNull(void* ptr) {
  return ptr==NULL;
}

char* getEnvPair(int i) {
    return *(environ + i);
}

void idris_memset(void* ptr, size_t offset, uint8_t c, size_t size) {
  memset(((uint8_t*)ptr) + offset, c, size);
}

uint8_t idris_peek(void* ptr, size_t offset) {
  return *(((uint8_t*)ptr) + offset);
}

void idris_poke(void* ptr, size_t offset, uint8_t data) {
  *(((uint8_t*)ptr) + offset) = data;
}

void idris_memmove(void* dest, void* src, size_t dest_offset, size_t src_offset, size_t size) {
  memmove(dest + dest_offset, src + src_offset, size);
}

void *__idris_gmpMalloc(size_t size) {
  return GC_malloc(size);
}

void *__idris_gmpRealloc(void *ptr, size_t oldSize, size_t size) {
  return GC_realloc(ptr, size);
}

void __idris_gmpFree(void *ptr, size_t oldSize) {
  GC_free(ptr);
}

char *__idris_strRev(const char *s) {
  int x = strlen(s);
  int y = 0;
  char *t = GC_malloc(x+1);

  t[x] = '\0';
  while(x>0) {
    t[y++] = s[--x];
  }
  return t;
}
