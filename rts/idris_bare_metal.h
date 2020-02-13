#ifndef _IDRIS_BARE_METAL_H
#define _IDRIS_BARE_METAL_H

#undef assert
#define assert(...)
#define printf(...)
#define fprintf(...)

#define puts(...)
#define fflush(...)

#define abort(...)
#define exit(...)

#endif
