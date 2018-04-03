#ifndef _IDRISBITSTRING_H
#define _IDRISBITSTRING_H

VAL idris_b8(VM *vm, VAL a);
VAL idris_b16(VM *vm, VAL a);
VAL idris_b32(VM *vm, VAL a);
VAL idris_b64(VM *vm, VAL a);
VAL idris_castB32Int(VM *vm, VAL a);
VAL idris_b8const(VM *vm, uint8_t a);
VAL idris_b16const(VM *vm, uint16_t a);
VAL idris_b32const(VM *vm, uint32_t a);
VAL idris_b64const(VM *vm, uint64_t a);

VAL idris_b8Plus(VM *vm, VAL a, VAL b);
VAL idris_b8Minus(VM *vm, VAL a, VAL b);
VAL idris_b8Times(VM *vm, VAL a, VAL b);
VAL idris_b8UDiv(VM *vm, VAL a, VAL b);
VAL idris_b8SDiv(VM *vm, VAL a, VAL b);
VAL idris_b8URem(VM *vm, VAL a, VAL b);
VAL idris_b8SRem(VM *vm, VAL a, VAL b);
VAL idris_b8Lt(VM *vm, VAL a, VAL b);
VAL idris_b8Gt(VM *vm, VAL a, VAL b);
VAL idris_b8Eq(VM *vm, VAL a, VAL b);
VAL idris_b8Lte(VM *vm, VAL a, VAL b);
VAL idris_b8Gte(VM *vm, VAL a, VAL b);
VAL idris_b8Compl(VM *vm, VAL a);
VAL idris_b8And(VM *vm, VAL a, VAL b);
VAL idris_b8Or(VM *vm, VAL a, VAL b);
VAL idris_b8Neg(VM *vm, VAL a);
VAL idris_b8Xor(VM *vm, VAL a, VAL b);
VAL idris_b8Shl(VM *vm, VAL a, VAL b);
VAL idris_b8LShr(VM *vm, VAL a, VAL b);
VAL idris_b8AShr(VM *vm, VAL a, VAL b);

VAL idris_b16Eq(VM *vm, VAL a, VAL b);
VAL idris_b32Eq(VM *vm, VAL a, VAL b);
VAL idris_b64Eq(VM *vm, VAL a, VAL b);

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
VAL idris_b16URem(VM *vm, VAL a, VAL b);
VAL idris_b16SRem(VM *vm, VAL a, VAL b);
VAL idris_b16Lt(VM *vm, VAL a, VAL b);
VAL idris_b16Gt(VM *vm, VAL a, VAL b);
VAL idris_b16Eq(VM *vm, VAL a, VAL b);
VAL idris_b16Lte(VM *vm, VAL a, VAL b);
VAL idris_b16Gte(VM *vm, VAL a, VAL b);
VAL idris_b16Compl(VM *vm, VAL a);
VAL idris_b16And(VM *vm, VAL a, VAL b);
VAL idris_b16Or(VM *vm, VAL a, VAL b);
VAL idris_b16Neg(VM *vm, VAL a);
VAL idris_b16Xor(VM *vm, VAL a, VAL b);
VAL idris_b16Shl(VM *vm, VAL a, VAL b);
VAL idris_b16LShr(VM *vm, VAL a, VAL b);
VAL idris_b16AShr(VM *vm, VAL a, VAL b);

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
VAL idris_b32URem(VM *vm, VAL a, VAL b);
VAL idris_b32SRem(VM *vm, VAL a, VAL b);
VAL idris_b32Lt(VM *vm, VAL a, VAL b);
VAL idris_b32Gt(VM *vm, VAL a, VAL b);
VAL idris_b32Eq(VM *vm, VAL a, VAL b);
VAL idris_b32Lte(VM *vm, VAL a, VAL b);
VAL idris_b32Gte(VM *vm, VAL a, VAL b);
VAL idris_b32Compl(VM *vm, VAL a);
VAL idris_b32And(VM *vm, VAL a, VAL b);
VAL idris_b32Or(VM *vm, VAL a, VAL b);
VAL idris_b32Neg(VM *vm, VAL a);
VAL idris_b32Xor(VM *vm, VAL a, VAL b);
VAL idris_b32Shl(VM *vm, VAL a, VAL b);
VAL idris_b32LShr(VM *vm, VAL a, VAL b);
VAL idris_b32AShr(VM *vm, VAL a, VAL b);

VAL idris_b32Z64(VM *vm, VAL a);
VAL idris_b32S64(VM *vm, VAL a);
VAL idris_b32T8(VM *vm, VAL a);
VAL idris_b32T16(VM *vm, VAL a);

VAL idris_b64Plus(VM *vm, VAL a, VAL b);
VAL idris_b64Minus(VM *vm, VAL a, VAL b);
VAL idris_b64Times(VM *vm, VAL a, VAL b);
VAL idris_b64UDiv(VM *vm, VAL a, VAL b);
VAL idris_b64SDiv(VM *vm, VAL a, VAL b);
VAL idris_b64URem(VM *vm, VAL a, VAL b);
VAL idris_b64SRem(VM *vm, VAL a, VAL b);
VAL idris_b64Lt(VM *vm, VAL a, VAL b);
VAL idris_b64Gt(VM *vm, VAL a, VAL b);
VAL idris_b64Eq(VM *vm, VAL a, VAL b);
VAL idris_b64Lte(VM *vm, VAL a, VAL b);
VAL idris_b64Gte(VM *vm, VAL a, VAL b);
VAL idris_b64Compl(VM *vm, VAL a);
VAL idris_b64And(VM *vm, VAL a, VAL b);
VAL idris_b64Or(VM *vm, VAL a, VAL b);
VAL idris_b64Neg(VM *vm, VAL a);
VAL idris_b64Xor(VM *vm, VAL a, VAL b);
VAL idris_b64Shl(VM *vm, VAL a, VAL b);
VAL idris_b64LShr(VM *vm, VAL a, VAL b);
VAL idris_b64AShr(VM *vm, VAL a, VAL b);

VAL idris_b64T8(VM *vm, VAL a);
VAL idris_b64T16(VM *vm, VAL a);
VAL idris_b64T32(VM *vm, VAL a);

// memory access
VAL idris_peekB8(VM* vm, VAL ptr, VAL offset);
VAL idris_pokeB8(VAL ptr, VAL offset, VAL data);
VAL idris_peekB16(VM* vm, VAL ptr, VAL offset);
VAL idris_pokeB16(VAL ptr, VAL offset, VAL data);
VAL idris_peekB32(VM* vm, VAL ptr, VAL offset);
VAL idris_pokeB32(VAL ptr, VAL offset, VAL data);
VAL idris_peekB64(VM* vm, VAL ptr, VAL offset);
VAL idris_pokeB64(VAL ptr, VAL offset, VAL data);

#endif
