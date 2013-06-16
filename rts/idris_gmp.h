#ifndef _IDRISGMP_H
#define _IDRISGMP_H

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

#define GETMPZ(x) *((mpz_t*)((x)->info.ptr))

#endif
