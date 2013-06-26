#include <stdio.h>
#include <gmp.h>
#include <gc.h>
#include <string.h>

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
  char *result = GC_malloc_atomic(len);
  result[0] = c;
  memcpy(result+1, s, len);
  result[len+1] = 0;
  return result;
}
