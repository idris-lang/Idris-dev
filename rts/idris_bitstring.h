#ifndef _IDRISBITSTRING_H
#define _IDRISBITSTRING_H

VAL idris_b8CopyForGC(VM *vm, VAL a);
VAL idris_b16CopyForGC(VM *vm, VAL a);
VAL idris_b32CopyForGC(VM *vm, VAL a);
VAL idris_b64CopyForGC(VM *vm, VAL a);

VAL idris_b8(VM *vm, VAL a);
VAL idris_b16(VM *vm, VAL a);
VAL idris_b32(VM *vm, VAL a);
VAL idris_b64(VM *vm, VAL a);

VAL idris_b8Plus(VM *vm, VAL a, VAL b);
VAL idris_b8Minus(VM *vm, VAL a, VAL b);
VAL idris_b8Times(VM *vm, VAL a, VAL b);
VAL idris_b8UDiv(VM *vm, VAL a, VAL b);
VAL idris_b8SDiv(VM *vm, VAL a, VAL b);

VAL idris_b8Z16(VM *vm, VAL a);
VAL idris_b8Z32(VM *vm, VAL a);
VAL idris_b8Z64(VM *vm, VAL a);
VAL idris_b8S16(VM *vm, VAL a);
VAL idris_b8S32(VM *vm, VAL a);
VAL idris_b8S64(VM *vm, VAL a);

VAL idris_b16Plus(VM *vm, VAL a, VAL b);
VAL idris_b16Minus(VM *vm, VAL a, VAL b);
VAL idris_b16Times(VM *vm, VAL a, VAL b);
VAL idris_b16UDiv(VM *vm, VAL a, VAL b);
VAL idris_b16SDiv(VM *vm, VAL a, VAL b);

VAL idris_b16Z32(VM *vm, VAL a);
VAL idris_b16Z64(VM *vm, VAL a);
VAL idris_b16S32(VM *vm, VAL a);
VAL idris_b16S64(VM *vm, VAL a);
VAL idris_b16T8(VM *vm, VAL a);

VAL idris_b32Plus(VM *vm, VAL a, VAL b);
VAL idris_b32Minus(VM *vm, VAL a, VAL b);
VAL idris_b32Times(VM *vm, VAL a, VAL b);
VAL idris_b32UDiv(VM *vm, VAL a, VAL b);
VAL idris_b32SDiv(VM *vm, VAL a, VAL b);

VAL idris_b32Z64(VM *vm, VAL a);
VAL idris_b32S64(VM *vm, VAL a);
VAL idris_b32T8(VM *vm, VAL a);
VAL idris_b32T16(VM *vm, VAL a);

VAL idris_b64Plus(VM *vm, VAL a, VAL b);
VAL idris_b64Minus(VM *vm, VAL a, VAL b);
VAL idris_b64Times(VM *vm, VAL a, VAL b);
VAL idris_b64UDiv(VM *vm, VAL a, VAL b);
VAL idris_b64SDiv(VM *vm, VAL a, VAL b);

VAL idris_b64T8(VM *vm, VAL a);
VAL idris_b64T16(VM *vm, VAL a);
VAL idris_b64T32(VM *vm, VAL a);

#endif
