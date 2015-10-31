#ifndef _IDRIS_UTF8
#define _IDRIS_UTF8

#include <stdint.h>
#include <stdlib.h>

/* Various functions for dealing with UTF8 encoding. These are probably
   not very efficient (and I'm (EB) making no guarantees about their
   correctness.) Nevertheless, they mean that we can treat Strings as
   UFT8. Patches welcome :). */

typedef uint8_t utf8_byte;

// Pascal-style strings with their lengths.
typedef struct {
    size_t size;
    utf8_byte* str_data;
} SizedString;


// Get the number of encoding units in a UTF8 string (equivalent to strlen)
size_t idris_utf8_unitlen(const utf8_byte* s);
// Get length of a UTF8 encoded string in characters
unsigned int idris_utf8_strlen(SizedString s);
// Get number of bytes the first character takes in a string
unsigned int idris_utf8_charlen(SizedString str);
// Return int representation of string at an index.
// Assumes in bounds.
unsigned idris_utf8_index(utf8_byte* s, int j);
// Convert a char as an integer to a char* as a sized string.
// Caller responsible for freeing the underlying bytes.
SizedString idris_utf8_fromChar(unsigned int x);
// Reverse a UTF8 encoded string, putting the result in 'result'
utf8_byte* idris_utf8_rev(utf8_byte* s, utf8_byte* result, size_t length);
// Advance a pointer into a string by i UTF8 characters.
// Return original pointer if i <= 0.
utf8_byte* idris_utf8_advance(utf8_byte* str, size_t length, int i);
#endif
