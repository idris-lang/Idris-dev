#include "idris_rts.h"

VAL idris_b8CopyForGC(VM *vm, VAL a) {
    uint8_t A = a->info.bits8;
    VAL cl = allocate(sizeof(Closure), 1);
    SETTY(cl, BITS8);
    cl->info.bits8 = A;
    return cl;
}

VAL idris_b16CopyForGC(VM *vm, VAL a) {
    uint16_t A = a->info.bits16;
    VAL cl = allocate(sizeof(Closure), 1);
    SETTY(cl, BITS16);
    cl->info.bits16 = A;
    return cl;
}

VAL idris_b32CopyForGC(VM *vm, VAL a) {
    uint32_t A = a->info.bits32;
    VAL cl = allocate(sizeof(Closure), 1);
    SETTY(cl, BITS32);
    cl->info.bits32 = A;
    return cl;
}

VAL idris_b64CopyForGC(VM *vm, VAL a) {
    uint64_t A = a->info.bits64;
    VAL cl = allocate(sizeof(Closure), 1);
    SETTY(cl, BITS64);
    cl->info.bits64 = A;
    return cl;
}

VAL idris_b8(VM *vm, VAL a) {
    uint8_t A = GETINT(a);
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) A;
    return cl;
}

VAL idris_b16(VM *vm, VAL a) {
    uint16_t A = GETINT(a);
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) A;
    return cl;
}

VAL idris_b32(VM *vm, VAL a) {
    uint32_t A = GETINT(a);
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) A;
    return cl;
}

VAL idris_b64(VM *vm, VAL a) {
    uint64_t A = GETINT(a);
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) A;
    return cl;
}

VAL idris_castB32Int(VM *vm, VAL a) {
    return MKINT((i_int)a->info.bits32);
}

VAL idris_b8const(VM *vm, uint8_t a) {
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = a;
    return cl;
}

VAL idris_b16const(VM *vm, uint16_t a) {
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = a;
    return cl;
}

VAL idris_b32const(VM *vm, uint32_t a) {
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = a;
    return cl;
}

VAL idris_b64const(VM *vm, uint64_t a) {
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = a;
    return cl;
}

VAL idris_b8Plus(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = A + B;
    return cl;
}

VAL idris_b8Minus(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = A - B;
    return cl;
}

VAL idris_b8Times(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = A * B;
    return cl;
}

VAL idris_b8UDiv(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = A / B;
    return cl;
}

VAL idris_b8SDiv(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) (((int8_t) A) / ((int8_t) B));
    return cl;
}

VAL idris_b8URem(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = A % B;
    return cl;
}

VAL idris_b8SRem(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) (((int8_t) A) % ((int8_t) B));
    return cl;
}

VAL idris_b8Lt(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits8 < b->info.bits8));
}

VAL idris_b8Gt(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits8 > b->info.bits8));
}

VAL idris_b8Eq(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits8 == b->info.bits8));
}

VAL idris_b8Lte(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits8 <= b->info.bits8));
}

VAL idris_b8Gte(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits8 >= b->info.bits8));
}

VAL idris_b8Compl(VM *vm, VAL a) {
    uint8_t A = a->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = ~ A;
    return cl;
}

VAL idris_b8And(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = A & B;
    return cl;
}

VAL idris_b8Or(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = A | B;
    return cl;
}

VAL idris_b8Xor(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = A ^ B;
    return cl;
}

VAL idris_b8Shl(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = A << B;
    return cl;
}

VAL idris_b8LShr(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = A >> B;
    return cl;
}

VAL idris_b8AShr(VM *vm, VAL a, VAL b) {
    uint8_t A = a->info.bits8;
    uint8_t B = b->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) (((int8_t) A) >> ((int8_t) B));
    return cl;
}

VAL idris_b16Plus(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = A + B;
    return cl;
}

VAL idris_b16Minus(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = A - B;
    return cl;
}

VAL idris_b16Times(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = A * B;
    return cl;
}

VAL idris_b16UDiv(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = A / B;
    return cl;
}

VAL idris_b16SDiv(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) (((int16_t) A) / ((int16_t) B));
    return cl;
}

VAL idris_b16URem(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = A % B;
    return cl;
}

VAL idris_b16SRem(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) (((int16_t) A) % ((int16_t) B));
    return cl;
}

VAL idris_b16Lt(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits16 < b->info.bits16));
}

VAL idris_b16Gt(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits16 > b->info.bits16));
}

VAL idris_b16Eq(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits16 == b->info.bits16));
}

VAL idris_b16Lte(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits16 <= b->info.bits16));
}

VAL idris_b16Gte(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits16 >= b->info.bits16));
}

VAL idris_b16Compl(VM *vm, VAL a) {
    uint16_t A = a->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = ~ A;
    return cl;
}

VAL idris_b16And(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = A & B;
    return cl;
}

VAL idris_b16Or(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = A | B;
    return cl;
}

VAL idris_b16Xor(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = A ^ B;
    return cl;
}

VAL idris_b16Shl(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = A << B;
    return cl;
}

VAL idris_b16LShr(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = A >> B;
    return cl;
}

VAL idris_b16AShr(VM *vm, VAL a, VAL b) {
    uint16_t A = a->info.bits16;
    uint16_t B = b->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) (((int16_t) A) >> ((int16_t) B));
    return cl;
}

VAL idris_b32Plus(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = A + B;
    return cl;
}

VAL idris_b32Minus(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = A - B;
    return cl;
}

VAL idris_b32Times(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = A * B;
    return cl;
}

VAL idris_b32UDiv(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = A / B;
    return cl;
}

VAL idris_b32SDiv(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) (((int32_t) A) / ((int32_t) B));
    return cl;
}

VAL idris_b32URem(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = A % B;
    return cl;
}

VAL idris_b32SRem(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) (((int32_t) A) % ((int32_t) B));
    return cl;
}

VAL idris_b32Lt(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits32 < b->info.bits32));
}

VAL idris_b32Gt(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits32 > b->info.bits32));
}

VAL idris_b32Eq(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits32 == b->info.bits32));
}

VAL idris_b32Lte(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits32 <= b->info.bits32));
}

VAL idris_b32Gte(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits32 >= b->info.bits32));
}

VAL idris_b32Compl(VM *vm, VAL a) {
    uint32_t A = a->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = ~ A;
    return cl;
}

VAL idris_b32And(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = A & B;
    return cl;
}

VAL idris_b32Or(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = A | B;
    return cl;
}

VAL idris_b32Xor(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = A ^ B;
    return cl;
}

VAL idris_b32Shl(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = A << B;
    return cl;
}

VAL idris_b32LShr(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = A >> B;
    return cl;
}

VAL idris_b32AShr(VM *vm, VAL a, VAL b) {
    uint32_t A = a->info.bits32;
    uint32_t B = b->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) (((int32_t)A) >> ((int32_t)B));
    return cl;
}

VAL idris_b64Plus(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = A + B;
    return cl;
}

VAL idris_b64Minus(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = A - B;
    return cl;
}

VAL idris_b64Times(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = A * B;
    return cl;
}

VAL idris_b64UDiv(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = A / B;
    return cl;
}

VAL idris_b64SDiv(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) (((int64_t) A) / ((int64_t) B));
    return cl;
}

VAL idris_b64URem(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = A % B;
    return cl;
}

VAL idris_b64SRem(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) (((int64_t) A) % ((int64_t) B));
    return cl;
}

VAL idris_b64Lt(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits64 < b->info.bits64));
}

VAL idris_b64Gt(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits64 > b->info.bits64));
}

VAL idris_b64Eq(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits64 == b->info.bits64));
}

VAL idris_b64Lte(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits64 <= b->info.bits64));
}

VAL idris_b64Gte(VM *vm, VAL a, VAL b) {
    return MKINT((i_int) (a->info.bits64 >= b->info.bits64));
}

VAL idris_b64Compl(VM *vm, VAL a) {
    uint64_t A = a->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = ~ A;
    return cl;
}

VAL idris_b64And(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = A & B;
    return cl;
}

VAL idris_b64Or(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = A | B;
    return cl;
}

VAL idris_b64Xor(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = A ^ B;
    return cl;
}

VAL idris_b64Shl(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = A << B;
    return cl;
}

VAL idris_b64LShr(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = A >> B;
    return cl;
}

VAL idris_b64AShr(VM *vm, VAL a, VAL b) {
    uint64_t A = a->info.bits64;
    uint64_t B = b->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) (((int64_t) A) >> ((int64_t) B));
    return cl;
}

VAL idris_b8Z16(VM *vm, VAL a) {
    uint8_t A = a->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) A;
    return cl;
}

VAL idris_b8Z32(VM *vm, VAL a) {
    uint8_t A = a->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) A;
    return cl;
}

VAL idris_b8Z64(VM *vm, VAL a) {
    uint8_t A = a->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) A;
    return cl;
}

VAL idris_b8S16(VM *vm, VAL a) {
    uint8_t A = a->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) (int16_t) (int8_t) A;
    return cl;
}

VAL idris_b8S32(VM *vm, VAL a) {
    uint8_t A = a->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) (int32_t) (int8_t) A;
    return cl;
}

VAL idris_b8S64(VM *vm, VAL a) {
    uint8_t A = a->info.bits8;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) (int64_t) (int8_t) A;
    return cl;
}

VAL idris_b16Z32(VM *vm, VAL a) {
    uint16_t A = a->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) A;
    return cl;
}

VAL idris_b16Z64(VM *vm, VAL a) {
    uint16_t A = a->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) A;
    return cl;
}

VAL idris_b16S32(VM *vm, VAL a) {
    uint16_t A = a->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) (int32_t) (int16_t) A;
    return cl;
}

VAL idris_b16S64(VM *vm, VAL a) {
    uint16_t A = a->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) (int64_t) (int16_t) A;
    return cl;
}

VAL idris_b16T8(VM *vm, VAL a) {
    uint16_t A = a->info.bits16;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) A;
    return cl;
}

VAL idris_b32Z64(VM *vm, VAL a) {
    uint32_t A = a->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) A;
    return cl;
}

VAL idris_b32S64(VM *vm, VAL a) {
    uint32_t A = a->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) (int64_t) (int32_t) A;
    return cl;
}

VAL idris_b32T8(VM *vm, VAL a) {
    uint32_t A = a->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) A;
    return cl;
}

VAL idris_b32T16(VM *vm, VAL a) {
    uint32_t A = a->info.bits32;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) A;
    return cl;
}

VAL idris_b64T8(VM *vm, VAL a) {
    uint64_t A = a->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) A;
    return cl;
}

VAL idris_b64T16(VM *vm, VAL a) {
    uint64_t A = a->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) A;
    return cl;
}

VAL idris_b64T32(VM *vm, VAL a) {
    uint64_t A = a->info.bits64;
    VAL cl = allocate(sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) A;
    return cl;
}

// SSE vectors
VAL idris_IDXB8x16(VM* vm, VAL vec, VAL idx) {
    __m128i sse = *vec->info.bits128p;
    uint8_t data[16];
    _mm_storeu_si128((__m128i*)&data, sse);
    return MKB8(vm, data[idx->info.bits32]);
}

VAL idris_IDXB16x8(VM* vm, VAL vec, VAL idx) {
    __m128i sse = *vec->info.bits128p;
    uint16_t data[8];
    _mm_storeu_si128((__m128i*)&data, sse);
    return MKB16(vm, data[idx->info.bits32]);
}

VAL idris_IDXB32x4(VM* vm, VAL vec, VAL idx) {
    __m128i sse = *vec->info.bits128p;
    uint32_t data[4];
    _mm_storeu_si128((__m128i*)&data, sse);
    return MKB32(vm, data[idx->info.bits32]);
}

VAL idris_IDXB64x2(VM* vm, VAL vec, VAL idx) {
     __m128i sse = *vec->info.bits128p;
    uint64_t data[2];
    _mm_storeu_si128((__m128i*)&data, sse);
    return MKB64(vm, data[idx->info.bits32]);
}
