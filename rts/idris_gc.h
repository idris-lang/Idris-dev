#ifndef _IDRISGC_H
#define _IDRISGC_H

#include "idris_rts.h"

void gc(VM* vm);
void gcInfo(VM* vm, int doGC);

#endif
