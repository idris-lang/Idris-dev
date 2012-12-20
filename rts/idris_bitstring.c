#include "idris_rts.h"

VAL idris_b8CopyForGC(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 1);
    SETTY(cl, BITS8);
    cl->info.bits8 = a->info.bits8;
    return cl;
}

VAL idris_b16CopyForGC(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 1);
    SETTY(cl, BITS16);
    cl->info.bits16 = a->info.bits16;
    return cl;
}

VAL idris_b32CopyForGC(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 1);
    SETTY(cl, BITS32);
    cl->info.bits32 = a->info.bits32;
    return cl;
}

VAL idris_b64CopyForGC(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 1);
    SETTY(cl, BITS64);
    cl->info.bits64 = a->info.bits64;
    return cl;
}

VAL idris_b8(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) GETINT(a);
    return cl;
}

VAL idris_b16(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) GETINT(a);
    return cl;
}

VAL idris_b32(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) GETINT(a);
    return cl;
}

VAL idris_b64(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) GETINT(a);
    return cl;
}

VAL idris_b8Plus(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = a->info.bits8 + b->info.bits8;
    return cl;
}

VAL idris_b8Minus(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = a->info.bits8 - b->info.bits8;
    return cl;
}

VAL idris_b8Times(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = a->info.bits8 * b->info.bits8;
    return cl;
}

VAL idris_b8UDiv(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = a->info.bits8 / b->info.bits8;
    return cl;
}

VAL idris_b8SDiv(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) (((int8_t) a->info.bits8) / ((int8_t) b->info.bits8));
    return cl;
}

VAL idris_b8Z16(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) a->info.bits8;
    return cl;
}

VAL idris_b8Z32(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) a->info.bits8;
    return cl;
}

VAL idris_b8Z64(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits64 = (uint64_t) a->info.bits8;
    return cl;
}

VAL idris_b8S16(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) (int16_t) (int8_t) a->info.bits8;
    return cl;
}

VAL idris_b8S32(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) (int32_t) (int8_t) a->info.bits8;
    return cl;
}

VAL idris_b8S64(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) (int64_t) (int8_t) a->info.bits8;
    return cl;
}

VAL idris_b16Plus(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = a->info.bits16 + b->info.bits16;
    return cl;
}

VAL idris_b16Minus(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = a->info.bits16 - b->info.bits16;
    return cl;
}

VAL idris_b16Times(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = a->info.bits16 * b->info.bits16;
    return cl;
}

VAL idris_b16UDiv(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = a->info.bits16 / b->info.bits16;
    return cl;
}

VAL idris_b16SDiv(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 =
      (uint16_t) (((int16_t) a->info.bits16) / ((int16_t) b->info.bits16));
    return cl;
}

VAL idris_b16Z32(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) a->info.bits16;
    return cl;
}

VAL idris_b16Z64(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) a->info.bits16;
    return cl;
}

VAL idris_b16S32(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) (int32_t) (int16_t) a->info.bits16;
    return cl;
}

VAL idris_b16S64(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) (int64_t) (int16_t) a->info.bits16;
    return cl;
}

VAL idris_b16T8(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) a->info.bits16;
    return cl;
}

VAL idris_b32Plus(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = a->info.bits32 + b->info.bits32;
    return cl;
}

VAL idris_b32Minus(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = a->info.bits32 - b->info.bits32;
    return cl;
}

VAL idris_b32Times(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = a->info.bits32 * b->info.bits32;
    return cl;
}

VAL idris_b32UDiv(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = a->info.bits32 / b->info.bits32;
    return cl;
}

VAL idris_b32SDiv(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 =
      (uint32_t) (((int32_t) a->info.bits32) / ((int32_t) b->info.bits32));
    return cl;
}

VAL idris_b32Z64(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) a->info.bits32;
    return cl;
}

VAL idris_b32S64(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = (uint64_t) (int64_t) (int32_t) a->info.bits32;
    return cl;
}

VAL idris_b32T8(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) a->info.bits32;
    return cl;
}

VAL idris_b32T16(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) a->info.bits32;
    return cl;
}

VAL idris_b64Plus(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = a->info.bits64 + b->info.bits64;
    return cl;
}

VAL idris_b64Minus(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = a->info.bits64 - b->info.bits64;
    return cl;
}

VAL idris_b64Times(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = a->info.bits64 * b->info.bits64;
    return cl;
}

VAL idris_b64UDiv(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 = a->info.bits64 / b->info.bits64;
    return cl;
}

VAL idris_b64SDiv(VM *vm, VAL a, VAL b) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS64);
    cl->info.bits64 =
      (uint64_t) (((int64_t) a->info.bits64) / ((int64_t) b->info.bits64));
    return cl;
}

VAL idris_b64T8(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS8);
    cl->info.bits8 = (uint8_t) a->info.bits64;
    return cl;
}

VAL idris_b64T16(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS16);
    cl->info.bits16 = (uint16_t) a->info.bits64;
    return cl;
}

VAL idris_b64T32(VM *vm, VAL a) {
    VAL cl = allocate(vm, sizeof(Closure), 0);
    SETTY(cl, BITS32);
    cl->info.bits32 = (uint32_t) a->info.bits64;
    return cl;
}

