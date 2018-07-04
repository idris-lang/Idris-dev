#ifndef _IDRISGMP_H
#define _IDRISGMP_H

#ifdef IDRIS_GMP
#include <gmp.h>
#else
#include "mini-gmp.h"
#endif

#include "idris_rts.h"

// Set memory allocation functions
void init_gmpalloc(void);

VAL MKBIGI(int val);
VAL MKBIGC(VM* vm, char* bigint);
VAL MKBIGM(VM* vm, void* bigint);
VAL MKBIGMc(VM* vm, void* bigint);
VAL MKBIGUI(VM* vm, unsigned long val);
VAL MKBIGSI(VM* vm, signed long val);

VAL idris_bigPlus(VM*, VAL x, VAL y);
VAL idris_bigMinus(VM*, VAL x, VAL y);
VAL idris_bigTimes(VM*, VAL x, VAL y);
VAL idris_bigDivide(VM*, VAL x, VAL y);
VAL idris_bigMod(VM*, VAL x, VAL y);

int bigEqConst(VAL x, int c);

VAL idris_bigEq(VM*, VAL x, VAL y);
VAL idris_bigLt(VM*, VAL x, VAL y);
VAL idris_bigLe(VM*, VAL x, VAL y);
VAL idris_bigGt(VM*, VAL x, VAL y);
VAL idris_bigGe(VM*, VAL x, VAL y);

VAL idris_castIntBig(VM* vm, VAL i);
VAL idris_castBigInt(VM* vm, VAL i);
VAL idris_castFloatBig(VM* vm, VAL i);
VAL idris_castBigFloat(VM* vm, VAL i);
VAL idris_castStrBig(VM* vm, VAL i);
VAL idris_castBigStr(VM* vm, VAL i);

VAL idris_bigAnd(VM* vm, VAL x, VAL y);
VAL idris_bigOr(VM* vm, VAL x, VAL y);
VAL idris_bigShiftLeft(VM* vm, VAL x, VAL y);
VAL idris_bigAShiftRight(VM* vm, VAL x, VAL y);
VAL idris_bigLShiftRight(VM* vm, VAL x, VAL y);

uint64_t idris_truncBigB64(const mpz_t bi);

static inline mpz_t * getmpz(BigInt * v) {
    return (mpz_t*)(v->big);
}

#define GETMPZ(x) *getmpz((BigInt*)x)

#endif
