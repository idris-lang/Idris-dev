#ifndef _IDRIS_UTF8
#define _IDRIS_UTF8

/* Various functions for dealing with UTF8 encoding. These are probably
   not very efficient (and I'm (EB) making no guarantees about their
   correctness.) Nevertheless, they mean that we can treat Strings as
   UFT8. Patches welcome :). */

// Get length of a UTF8 encoded string in characters
int idris_utf8_strlen(char *s);
// Get number of bytes the first character takes in a string
int idris_utf8_charlen(char* s);
// Return int representation of string at an index.
// Assumes in bounds.
unsigned idris_utf8_index(char* s, int j);
// Convert a char as an integer to a char* as a byte sequence
// Null terminated; caller responsible for freeing
char* idris_utf8_fromChar(int x);
// Reverse a UTF8 encoded string, putting the result in 'result'
char* idris_utf8_rev(char* s, char* result);
// Advance a pointer into a string by i UTF8 characters.
// Return original pointer if i <= 0.
char* idris_utf8_advance(char* str, int i);
// Return the offset of the ith UTF8 character in the string
int idris_utf8_findOffset(char* str, int i);
#endif
