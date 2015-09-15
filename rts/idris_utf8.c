#include "idris_utf8.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

size_t idris_utf8_unitlen(const utf8_byte* s) {
    return strlen((const char*) s);
}

unsigned int idris_utf8_strlen(SizedString s) {
   unsigned int i = 0, j = 0;
   while (i < s.size) {
     if ((s.str_data[i] & 0xc0) != 0x80) j++;
     i++;
   }
   return j;
}

unsigned int idris_utf8_charlen(SizedString str) {
    if (str.size < 1) {
        fprintf(stderr, "Tried to take the first character of the empty string.\n");
        exit(EXIT_FAILURE);
    }
    utf8_byte init = str.str_data[0];
    if ((init & 0x80) == 0) {
        return 1; // Top bit unset, so 1 byte
    }
    if ((init > 244 && init < 256) ||
        (init == 192) ||
        (init == 193)) {
        return 1; // Invalid characters
    }
    unsigned int i = 1;
    while ((str.str_data[i] & 0xc0) == 0x80) {
        i++; // Move on until top 2 bits are not 10
        if (i >= str.size) {
            fprintf(stderr, "Malformed UTF-8 character extends past length of string.\n");
            exit(EXIT_FAILURE);
        }
    }
    return i;
}

unsigned idris_utf8_index(utf8_byte* s, int idx) {
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

utf8_byte* idris_utf8_advance(utf8_byte* str, size_t len, int i) {
    utf8_byte *end = str + len;
    while (i > 0 && str < end) {
        // In a UTF8 single-byte char, the highest bit is 0.  In the
        // first byte of a multi-byte char, the highest two bits are
        // 11, but the rest of the bytes start with 10. So we can
        // decrement our character counter when we see something other
        // than 10 at the front.
        if ((*str & 0xc0) != 0x80) {
            i--;
        }
        str++;
    }
    // Now we've found the first byte of the last character. Advance
    // to the end of it, or the end of the string, whichever is first.
    while ((*str & 0xc0) == 0x80 && str < end) { str++; }

    return str;
}


SizedString idris_utf8_fromChar(unsigned int x) {
    utf8_byte* str;
    int bytes = 0, top = 0;
    size_t size = 0;

    if (x > 1114112) {
        fprintf(stderr, "%i is larger than the largest Unicode code point", x);
        exit(EXIT_FAILURE);
    }

    // Character requires a single byte - bits above 7 are all unset
    if (x < 0x80) {
        // Caller will free
        str = malloc(2);
        if (str == NULL) {
            fprintf(stderr, "Couldn't allocate for character");
            exit(EXIT_FAILURE);
        }
        str[0] = (utf8_byte)x;
        str[1] = '\0';
        SizedString res = {.size = 1, .str_data = str};
        return res;
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

    // Caller will free
    str = malloc(bytes + 1);
    size = bytes;
    if (str == NULL) {
        fprintf(stderr, "Couldn't allocate for character");
        exit(EXIT_FAILURE);
    }
    str[bytes] = '\0';
    while(bytes > 0) {
        int xbits = x & 0x3f; // Next 6 bits
        bytes--;
        if (bytes > 0) {
            str[bytes] = (utf8_byte)xbits + 0x80;
        } else {
            str[0] = (utf8_byte)xbits + top;
        }
        x = x >> 6;
    }

    SizedString res = {.size = size, .str_data = str};
    return res;
}

void reverse_range(utf8_byte *start, utf8_byte *end) {
    while(start < end) {
        utf8_byte c = *start;
        *start++ = *end;
        *end-- = c;
    }
}

utf8_byte* reverse_char(utf8_byte *start) {
    utf8_byte *end = start;
    while((end[1] & 0xc0) == 0x80) { end++; }
    reverse_range(start, end);
    return (end + 1);
}

utf8_byte* idris_utf8_rev(utf8_byte* s, utf8_byte* result, size_t length) {
    memcpy(result, s, length);
    utf8_byte* end = result;
    while(end < result + length) { end = reverse_char(end); }
    reverse_range(result, result + length - 1);
    return result;
}

