#include "idris_rts.h"
#include <gmp.h>
#include <stdlib.h>
#include <string.h>

VAL MKBIGI(int val) {
    return MKINT((i_int)val);
}

VAL MKBIGC(VM* vm, char* val) {
    mpz_t* bigint;
    
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                          sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));
    
    mpz_init(*bigint);
    mpz_set_str(*bigint, val, 10);

    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;

    return cl;
}

VAL MKBIGM(VM* vm, void* big) {
    mpz_t* bigint;
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                          sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));

    mpz_init(*bigint);
    mpz_set(*bigint, *((mpz_t*)big));

    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;

    return cl;
}

VAL MKBIGMc(VM* vm, void* big) {
    mpz_t* bigint;
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                          sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));

    mpz_init_set(*bigint, *((mpz_t*)big));

    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;

    return cl;
}

VAL MKBIGUI(VM* vm, unsigned long val) {
    mpz_t* bigint;
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                          sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));

    mpz_init_set_ui(*bigint, val);

    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;

    return cl;
}

VAL MKBIGSI(VM* vm, signed long val) {
    mpz_t* bigint;
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                          sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));

    mpz_init_set_si(*bigint, val);

    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;

    return cl;
}

VAL GETBIG(VM * vm, VAL x) {
    if (ISINT(x)) {
        mpz_t* bigint;
        VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                              sizeof(mpz_t), 0);
        bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));

        mpz_init(*bigint);
        mpz_set_si(*bigint, GETINT(x));

        SETTY(cl, BIGINT);
        cl -> info.ptr = (void*)bigint;

        return cl;
    } else {
        return x;
    }
}

VAL bigAdd(VM* vm, VAL x, VAL y) {
    mpz_t* bigint;
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                          sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));
    mpz_add(*bigint, GETMPZ(x), GETMPZ(y));
    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;
    return cl;
}

VAL bigSub(VM* vm, VAL x, VAL y) {
    mpz_t* bigint;
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                          sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));
    mpz_sub(*bigint, GETMPZ(x), GETMPZ(y));
    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;
    return cl;
}

VAL bigMul(VM* vm, VAL x, VAL y) {
    mpz_t* bigint;
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                          sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));
    mpz_mul(*bigint, GETMPZ(x), GETMPZ(y));
    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;
    return cl;
}

VAL bigDiv(VM* vm, VAL x, VAL y) {
    mpz_t* bigint;
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                          sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));
    mpz_div(*bigint, GETMPZ(x), GETMPZ(y));
    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;
    return cl;
}

VAL bigMod(VM* vm, VAL x, VAL y) {
    mpz_t* bigint;
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                          sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));
    mpz_mod(*bigint, GETMPZ(x), GETMPZ(y));
    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;
    return cl;
}

VAL idris_bigPlus(VM* vm, VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
        i_int vx = GETINT(x);
        i_int vy = GETINT(y);
        if ((vx <= 0 && vy >=0) || (vx >=0 && vy <=0)) {
            return ADD(x, y);
        }
        i_int res = vx + vy;
        if (res >= 1<<30 || res <= -(1 << 30)) {
            return bigAdd(vm, GETBIG(vm, x), GETBIG(vm, y));
        } else {
            return MKINT(res);
        }
    } else {
        return bigAdd(vm, GETBIG(vm, x), GETBIG(vm, y));
    }
}

VAL idris_bigMinus(VM* vm, VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
        i_int vx = GETINT(x);
        i_int vy = GETINT(y);
        if ((vx <= 0 && vy <=0) || (vx >=0 && vy <=0)) {
            return INTOP(-, x, y);
        }
        i_int res = vx - vy;
        if (res >= 1<<30 || res <= -(1 << 30)) {
            return bigSub(vm, GETBIG(vm, x), GETBIG(vm, y));
        } else {
            return MKINT(res);
        }
    } else {
        return bigSub(vm, GETBIG(vm, x), GETBIG(vm, y));
    }
}

VAL idris_bigTimes(VM* vm, VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
        i_int vx = GETINT(x);
        i_int vy = GETINT(y);
	// we could work out likelihood of overflow by checking the number
	// of necessary bits. Here's a quick conservative hack instead.
	if ((vx < (1<<15) && vy < (1<16)) ||
	    (vx < (1<<16) && vy < (1<15)) ||
	    (vx < (1<<20) && vy < (1<11)) ||
	    (vx < (1<<11) && vy < (1<20)) ||
	    (vx < (1<<23) && vy < (1<<8)) ||
	    (vx < (1<<8) && vy < (1<<23))) { // ultra-conservative!
	    return INTOP(*,x,y);
        } else {
            return bigMul(vm, GETBIG(vm, x), GETBIG(vm, y));
        }
    } else {
        return bigMul(vm, GETBIG(vm, x), GETBIG(vm, y));
    }
}

VAL idris_bigDivide(VM* vm, VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
        return INTOP(/, x, y);
    } else {
        return bigDiv(vm, GETBIG(vm, x), GETBIG(vm, y));
    }
}

VAL idris_bigMod(VM* vm, VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
        return INTOP(%, x, y);
    } else {
        return bigMod(vm, GETBIG(vm, x), GETBIG(vm, y));
    }
}

int bigEqConst(VAL x, int c) {
    if (ISINT(x)) { return (GETINT(x) == c); }
    else { 
        int rv = mpz_cmp_si(GETMPZ(x), c); 
        return (rv == 0);
    }
}

VAL bigEq(VM* vm, VAL x, VAL y) {
    return MKINT((i_int)(mpz_cmp(GETMPZ(x), GETMPZ(y)) == 0));
}

VAL bigLt(VM* vm, VAL x, VAL y) {
    return MKINT((i_int)(mpz_cmp(GETMPZ(x), GETMPZ(y)) < 0));
}

VAL bigGt(VM* vm, VAL x, VAL y) {
    return MKINT((i_int)(mpz_cmp(GETMPZ(x), GETMPZ(y)) > 0));
}

VAL bigLe(VM* vm, VAL x, VAL y) {
    return MKINT((i_int)(mpz_cmp(GETMPZ(x), GETMPZ(y)) <= 0));
}

VAL bigGe(VM* vm, VAL x, VAL y) {
    return MKINT((i_int)(mpz_cmp(GETMPZ(x), GETMPZ(y)) >= 0));
}

VAL idris_bigEq(VM* vm, VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
        return MKINT((i_int)(GETINT(x) == GETINT(y)));
    } else {
        return bigEq(vm, GETBIG(vm, x), GETBIG(vm, y));
    }
}

VAL idris_bigLt(VM* vm, VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
        return MKINT((i_int)(GETINT(x) < GETINT(y)));
    } else {
        return bigLt(vm, GETBIG(vm, x), GETBIG(vm, y));
    }
}

VAL idris_bigLe(VM* vm, VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
        return MKINT((i_int)(GETINT(x) <= GETINT(y)));
    } else {
        return bigLe(vm, GETBIG(vm, x), GETBIG(vm, y));
    }
}

VAL idris_bigGt(VM* vm, VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
        return MKINT((i_int)(GETINT(x) > GETINT(y)));
    } else {
        return bigGt(vm, GETBIG(vm, x), GETBIG(vm, y));
    }
}

VAL idris_bigGe(VM* vm, VAL x, VAL y) {
    if (ISINT(x) && ISINT(y)) {
        return MKINT((i_int)(GETINT(x) >= GETINT(y)));
    } else {
        return bigGe(vm, GETBIG(vm, x), GETBIG(vm, y));
    }
}


VAL idris_castIntBig(VM* vm, VAL i) {
    return i;
}

VAL idris_castBigInt(VM* vm, VAL i) {
    if (ISINT(i)) {
        return i;
    } else {
        return MKINT((i_int)(mpz_get_ui(GETMPZ(i))));
    }
}

VAL idris_castBigFloat(VM* vm, VAL i) {
    if (ISINT(i)) {
        return MKFLOAT(vm, GETINT(i));
    } else {
        return MKFLOAT(vm, mpz_get_d(GETMPZ(i)));
    }
}

VAL idris_castFloatBig(VM* vm, VAL f) {
    double val = GETFLOAT(f);

    mpz_t* bigint;
    VAL cl = allocate(vm, sizeof(ClosureType) + sizeof(void*) + 
                      sizeof(mpz_t), 0);
    bigint = (mpz_t*)(((char*)cl) + sizeof(ClosureType) + sizeof(void*));

    mpz_init_set_d(*bigint, val);

    SETTY(cl, BIGINT);
    cl -> info.ptr = (void*)bigint;

    return cl;
}

VAL idris_castStrBig(VM* vm, VAL i) {
    return MKBIGC(vm, GETSTR(i));
}

VAL idris_castBigStr(VM* vm, VAL i) {
    char* str = mpz_get_str(NULL, 10, GETMPZ(GETBIG(vm, i)));
    return MKSTR(vm, str);
}

