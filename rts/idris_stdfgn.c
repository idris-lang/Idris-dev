#include "idris_stdfgn.h"
#include "idris_rts.h"
#include "idris_gmp.h"
#include "idris_gc.h"

#include <fcntl.h>
#include <errno.h>
#include <sys/stat.h>
#include <time.h>
#include <dirent.h>
#include <unistd.h>

#ifdef _WIN32
#include "windows/win_utils.h"
#else
#include <sys/select.h>
#endif

extern char** environ;

void putStr(char* str) {
    printf("%s", str);
}

void *fileOpen(char *name, char *mode) {
#ifdef _WIN32
    FILE *f = win32_u8fopen(name, mode);
#else
    FILE *f = fopen(name, mode);
#endif
    return (void *)f;
}

void fileClose(void* h) {
    FILE* f = (FILE*)h;
    fclose(f);
}

int fileEOF(void* h) {
    FILE* f = (FILE*)h;
    return feof(f);
}

int fileError(void* h) {
    FILE* f = (FILE*)h;
    return ferror(f);
}

int fileRemove(const char *filename) {
    return remove(filename);
}

int fileSize(void* h) {
    FILE* f = (FILE*)h;
    int fd = fileno(f);

    struct stat buf;
    if (fstat(fd, &buf) == 0) {
        return (int)(buf.st_size);
    } else {
        return -1;
    }
}

VAL fileAccessTime(void* h) {
    FILE* f = (FILE*)h;
    int fd = fileno(f);

    struct stat buf;
    if (fstat(fd, &buf) == 0) {
        return MKBIGI(buf.st_atime);
    } else {
        return MKBIGI(-1);
    }
}

VAL fileModifiedTime(void* h) {
    FILE* f = (FILE*)h;
    int fd = fileno(f);

    struct stat buf;
    if (fstat(fd, &buf) == 0) {
        return MKBIGI(buf.st_mtime);
    } else {
        return MKBIGI(-1);
    }
}

VAL fileStatusTime(void* h) {
    FILE* f = (FILE*)h;
    int fd = fileno(f);

    struct stat buf;
    if (fstat(fd, &buf) == 0) {
        return MKBIGI(buf.st_ctime);
    } else {
        return MKBIGI(-1);
    }
}

typedef struct {
    DIR* dirptr;
    int error;
} DirInfo;

void* idris_dirOpen(char* dname) {
    DIR *d = opendir(dname);
    if (d == NULL) {
        return NULL;
    } else {
        DirInfo* di = malloc(sizeof(DirInfo));
        di->dirptr = d;
        di->error = 0;

        return (void*)di;
    }
}

void idris_dirClose(void* h) {
    DirInfo* di = (DirInfo*)h;

    closedir(di->dirptr);
    free(di);
}

char* idris_nextDirEntry(void* h) {
    DirInfo* di = (DirInfo*)h;
    struct dirent* de = readdir(di->dirptr);

    if (de == NULL) {
        di->error = -1;
        return NULL;
    } else {
        return de->d_name;
    }
}

int idris_mkdir(char* dname) {
#ifdef _WIN32
    return mkdir(dname);
#else
    return mkdir(dname, S_IRWXU | S_IRGRP | S_IROTH);
#endif
}

int idris_chdir(char* dname) {
    return chdir(dname);
}

int idris_dirError(void *dptr) {
    return ((DirInfo*)dptr)->error;
}

int idris_writeStr(void* h, char* str) {
    FILE* f = (FILE*)h;
    if (fputs(str, f) >= 0) {
        return 0;
    } else {
        return -1;
    }
}

int fpoll(void* h)
{
#ifdef _WIN32
    return win_fpoll(h);
#else
    FILE* f = (FILE*)h;
    fd_set x;
    struct timeval timeout;
    timeout.tv_sec = 1;
    timeout.tv_usec = 0;
    int fd = fileno(f);

    FD_ZERO(&x);
    FD_SET(fd, &x);

    int r = select(fd+1, &x, 0, 0, &timeout);
    return r;
#endif
}

void *do_popen(const char *cmd, const char *mode) {
#ifdef _WIN32
    FILE *f = win32_u8popen(cmd, mode);
#else
    FILE *f = popen(cmd, mode);
    //    int d = fileno(f);
    //    fcntl(d, F_SETFL, O_NONBLOCK);
#endif
    return f;
}

void* idris_stdin() {
    return (void*)stdin;
}

char* getEnvPair(int i) {
    return *(environ + i);
}

VAL idris_time() {
    time_t t = time(NULL);
    return MKBIGI(t);
}

VAL idris_clock(VM* vm) {
    VAL result;
#ifdef _WIN32
    int64_t sec, nsec;
    win32_gettime(&sec, &nsec);
    idris_constructor(result, vm, 0, 2, 0);
    idris_setConArg(result, 0, MKBIGI(sec));
    idris_setConArg(result, 1, MKBIGI(nsec));
#else
    struct timespec ts;
    // We're not checking the result here, which is of course bad, but
    // CLOCK_REALTIME is required by POSIX at least!
    clock_gettime(CLOCK_REALTIME, &ts);
    idris_constructor(result, vm, 0, 2, 0);
    idris_setConArg(result, 0, MKBIGI(ts.tv_sec));
    idris_setConArg(result, 1, MKBIGI(ts.tv_nsec));
#endif
    return result;
}

#ifndef SEL4
#ifndef BARE_METAL
int idris_usleep(int usec) {
    struct timespec t;
    t.tv_sec = usec / 1000000;
    t.tv_nsec = (usec % 1000000) * 1000;

    return nanosleep(&t, NULL);
}
#endif // BARE_METAL
#endif // SEL4

VAL idris_mkFileError(VM* vm) {
    VAL result;
    switch(errno) {
        // Make sure this corresponds to the FileError structure in
        // Prelude.File
        case ENOENT:
            idris_constructor(result, vm, 3, 0, 0);
            break;
        case EACCES:
            idris_constructor(result, vm, 4, 0, 0);
            break;
        default:
            idris_constructor(result, vm, 0, 1, 0);
            idris_setConArg(result, 0, MKINT((intptr_t)errno));
            break;
    }
    return result;
}

void idris_forceGC(void* vm) {
    idris_gc((VM*)vm);
}

typedef struct {
    char* string;
    int len;
} StrBuffer;

void* idris_makeStringBuffer(int len) {
    StrBuffer* sb = malloc(sizeof(StrBuffer));
    if (sb != NULL) {
        sb->string = malloc(len);
        sb->string[0] = '\0';
        sb->len = 0;
    }
    return sb;
}

void idris_addToString(void* buffer, char* str) {
    StrBuffer* sb = (StrBuffer*)buffer;
    int len = strlen(str);

    memcpy(sb->string + sb->len, str, len+1);
    sb->len += len;
}

VAL idris_getString(VM* vm, void* buffer) {
    StrBuffer* sb = (StrBuffer*)buffer;

    VAL str = MKSTR(vm, sb->string);
    free(sb->string);
    free(sb);
    return str;
}

VAL idris_currentDir() {
   char cwd[1024];
   if (getcwd(cwd, sizeof(cwd)) != NULL)
     return MKSTR(get_vm(),cwd);
   else
     return MKSTR(get_vm(),"");
}
