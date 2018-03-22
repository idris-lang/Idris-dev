#include "idris_gmp.h"
#include "idris_opts.h"
#include "idris_rts.h"
#include "idris_stats.h"

void _idris__123_runMain_95_0_125_(VM* vm, VAL* oldbase);

#ifdef _WIN32

#include <Windows.h>

int win32_get_argv_utf8(int *argc_ptr, char ***argv_ptr)
{
    int argc;
    char **argv;
    wchar_t **argv_utf16 = CommandLineToArgvW(GetCommandLineW(), &argc);
    int i;
    int offset = (argc + 1) * sizeof(char *);
    int size = offset;
    for (i = 0; i < argc; i++) {
        size += WideCharToMultiByte(CP_UTF8, 0, argv_utf16[i], -1, 0, 0, 0, 0);
    }
    argv = (char **)malloc(size);
    for (i = 0; i < argc; i++) {
        argv[i] = (char *)argv + offset;
        offset += WideCharToMultiByte(CP_UTF8, 0, argv_utf16[i], -1, argv[i], size - offset, 0, 0);
    }
    *argc_ptr = argc;
    *argv_ptr = argv;
    return 0;
}

#endif

// The default options should give satisfactory results under many circumstances.
RTSOpts opts = {
    .init_heap_size = 16384000,
    .max_stack_size = 4096000,
    .show_summary   = 0
};

#ifdef _WIN32
int main() {
    int argc;
    char **argv;
    win32_get_argv_utf8(&argc, &argv);
#else
int main(int argc, char **argv) {
#endif
    parse_shift_args(&opts, &argc, &argv);

    __idris_argc = argc;
    __idris_argv = argv;

    VM* vm = init_vm(opts.max_stack_size, opts.init_heap_size, 1);
    init_threadkeys();
    init_threaddata(vm);
    init_gmpalloc();

    init_nullaries();
    init_signals();

    _idris__123_runMain_95_0_125_(vm, NULL);

#ifdef IDRIS_DEBUG
    if (opts.show_summary) {
        idris_gcInfo(vm, 1);
    }
#endif

    Stats stats = terminate(vm);

    if (opts.show_summary) {
        print_stats(&stats);
    }

    return EXIT_SUCCESS;
}
