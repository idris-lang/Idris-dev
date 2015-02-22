#include <windows.h>
#include <io.h>
#include <stdio.h>

// THis file exists to avoid clashes between windows.h and idris_rts.h
//

int win_fpoll(void* h)
{
    HANDLE wh =(HANDLE) _get_osfhandle(_fileno((FILE*)h));
    if (wh == INVALID_HANDLE_VALUE) {
        return -1;
    }
    DWORD ret = WaitForSingleObject(wh, 1000);
    // Imitate the return values of select()
    if (ret == WAIT_OBJECT_0)
        return 1;
    if (ret == WAIT_TIMEOUT)
        return 0;
    return -1;
}
