#include "idris_opts.h"
#include "idris_stats.h"
#include "idris_rts.h"
// The default options should give satisfactory results under many circumstances.
RTSOpts opts = { 
    .init_heap_size = 4096000,
    .max_stack_size = 4096000,
    .show_summary   = 0
};

int main(int argc, char* argv[]) {
    parse_shift_args(&opts, &argc, &argv);

    __idris_argc = argc;
    __idris_argv = argv;

    VM* vm = init_vm(opts.max_stack_size, opts.init_heap_size, 1);
    _idris__123_runMain0_125_(vm, NULL);

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
