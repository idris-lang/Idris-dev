#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <windows.h>


// THis file exists to avoid clashes between windows.h and idris_rts.h
//

int win_fpoll(void *h)
{
    HANDLE wh =(HANDLE) _get_osfhandle(_fileno((FILE *)h));
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

int widen_utf8(const char *filename_utf8, LPWSTR *filename_w)
{
    int num_chars = MultiByteToWideChar(CP_UTF8, 0, filename_utf8, -1, 0, 0);
    int size = sizeof(WCHAR);
    *filename_w = (LPWSTR)malloc(size * num_chars);
    MultiByteToWideChar(CP_UTF8, 0, filename_utf8, -1, *filename_w, num_chars);
    return num_chars;
}

FILE *win32_u8fopen(const char *path, const char *mode)
{
    LPWSTR wpath, wmode;
    widen_utf8(path, &wpath);
    widen_utf8(mode, &wmode);
    FILE *f = _wfopen(wpath, wmode);
    free(wpath);
    free(wmode);
    return f;
}

FILE *win32_u8popen(const char *path, const char *mode)
{
    LPWSTR wpath, wmode;
    widen_utf8(path, &wpath);
    widen_utf8(mode, &wmode);
    FILE *f = _wpopen(wpath, wmode);
    free(wpath);
    free(wmode);
    return f;
}

void win32_gettime(int64_t* sec, int64_t* nsec)
{
    FILETIME ft;
    GetSystemTimePreciseAsFileTime(&ft);
    ULARGE_INTEGER t;
    t.HighPart = ft.dwHighDateTime;
    t.LowPart = ft.dwLowDateTime;

    *nsec = (t.QuadPart % 10000000)*100;
    *sec = t.QuadPart / 10000000;
    *sec -= 11644473600; // LDAP epoch to Unix epoch 
}