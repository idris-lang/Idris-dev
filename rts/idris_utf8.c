#include "idris_utf8.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

int idris_utf8_strlen(char *s) {
   int i = 0, j = 0;
   while (s[i]) {
     if ((s[i] & 0xc0) != 0x80) j++;
     i++;
   }
   return j;
}

int idris_utf8_charlen(char* s) {
    int init = (int)s[0];
    if ((init & 0x80) == 0) {
        return 1; // Top bit unset, so 1 byte
    }
    if ((init > 244 && init < 256) ||
        (init == 192) ||
        (init == 193)) {
        return 1; // Invalid characters
    }
    int i = 1;
    while ((s[i] & 0xc0) == 0x80) {
        i++; // Move on until top 2 bits are not 10
    }
    return i;
}

unsigned idris_utf8_index(char* s, int idx) {
   int i = 0, j = 0;
   while (j < idx) {
     if ((s[i] & 0xc0) != 0x80) j++;
     i++;
   }
   // Find the start of the next character
   while ((s[i] & 0xc0) == 0x80) { i++; }

   unsigned bytes = 0;
   unsigned top = 0;

   int init = (int)s[1];

   // s[i] is now the start of the character we want
   if ((s[i] & 0x80) == 0) {
       bytes = 1;
       top = (int)(s[i]);
   } else if ((init > 244 && init < 256) ||
              (init == 192) ||
              (init == 193)) {
       bytes = 1;
       top = (int)(s[i]); // Invalid characters
   } else if ((s[i] & 0xe0) == 0xc0) {
       bytes = 2;
       top = (int)(s[i] & 0x1f); // 5 bits
   } else if ((s[i] & 0xf0) == 0xe0) {
       bytes = 3;
       top = (int)(s[i] & 0x0f); // 4 bits
   } else if ((s[i] & 0xf8) == 0xf0) {
       bytes = 4;
       top = (int)(s[i] & 0x07); // 3 bits
   } else if ((s[i] & 0xfc) == 0xf8) {
       bytes = 5;
       top = (int)(s[i] & 0x03); // 2 bits
   } else if ((s[i] & 0xfe) == 0xfc) {
       bytes = 6;
       top = (int)(s[i] & 0x01); // 1 bits
   }

   while (bytes > 1) {
       top = top << 6;
       top += s[++i] & 0x3f; // 6 bits
       --bytes;
   }

   return top;
}

char* idris_utf8_advance(char* str, int i) {
    // The pointer is not at the beginning of a character - find the next one
    while ((*str & 0xc0) == 0x80) { str++; }

    // Scan characters i times, but bail on end of string
    while (i > 0 && *str != '\0') {
        if ((*str & 0x80) == 0) {
            str += 1;
        }  else if ((*str & 0xe0) == 0xc0) {
            str += 2;
        } else if ((*str & 0xf0) == 0xe0) {
            str += 3;
        } else if ((*str & 0xf8) == 0xf0) {
            str += 4;
        } else if ((*str & 0xfc) == 0xf8) {
            str += 5;
        } else if ((*str & 0xfe) == 0xfc) {
            str += 6;
        } else {
            // This shouldn't happen - it means that the string is ill-formed.
            // Assume we got a normal C string, and advance by one char.
            str++;
        }
        i--;
    }

    return str;
}


char* idris_utf8_fromChar(int x) {
    char* str;
    int bytes = 0, top = 0;

    if ((x & 0x80) == 0) {
        str = malloc(2);
        str[0] = (char)x;
        str[1] = '\0';
        return str;
    }

    if (x >= 0x80 && x <= 0x7ff) {
        bytes = 2;
        top = 0xc0;
    } else if (x >= 0x800 && x <= 0xffff) {
        bytes = 3;
        top = 0xe0;
    } else if (x >= 0x10000 && x <= 0x10ffff) {
        bytes = 4;
        top = 0xf0;
    }

    str = malloc(bytes + 1);
    str[bytes] = '\0';
    while(bytes > 0) {
        int xbits = x & 0x3f; // Next 6 bits
        bytes--;
        if (bytes > 0) {
            str[bytes] = (char)xbits + 0x80;
        } else {
            str[0] = (char)xbits + top;
        }
        x = x >> 6;
    }

    return str;
}

void reverse_range(char *start, char *end)
{
    while(start < end)
    {
        char c = *start;
        *start++ = *end;
        *end-- = c;
    }
}

char* reverse_char(char *start)
{
    char *end = start;
    while((end[1] & 0xc0) == 0x80) { end++; }
    reverse_range(start, end);
    return(end + 1);
}

char* idris_utf8_rev(char* s, char* result) {
    strcpy(result, s);
    char* end = result;
    while(*end) { end = reverse_char(end); }
    reverse_range(result, end-1);
    return result;
}

