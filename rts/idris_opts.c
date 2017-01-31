#include "idris_opts.h"

#include <stdlib.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>


#define USAGE "\n"                                              \
    "Usage: <prog> [+RTS <rtsopts> -RTS] <args>\n\n"            \
    "Options:\n\n"                                              \
    "  -?    Print this message and exits.\n"                   \
    "  -s    Summary GC statistics.\n"                          \
    "  -H    Initial heap size. Egs: -H4M, -H500K, -H1G\n"      \
    "  -K    Sets the maximum stack size. Egs: -K8M\n"          \
    "\n"

void print_usage(FILE * s) {
    fprintf(s, USAGE);
}

int read_size(char * str) {
    int size = 0;
    char mult = ' ';

    int r = sscanf(str, "%u%c", &size, &mult);

    if (r == 1)
        return size;

    if (r == 2) {
        switch (mult) {
        case 'K': size = size << 10; break;
        case 'M': size = size << 20; break;
        case 'G': size = size << 30; break;
        default:
            fprintf(stderr,
                    "RTS Opts: Unable to recognize size suffix `%c'.\n" \
                    "          Possible suffixes are K or M or G.\n",
                    mult);
            print_usage(stderr);
            exit(EXIT_FAILURE);
        }
        return size;
    }

    fprintf(stderr, "RTS Opts: Unable to parse size. Egs: 1K, 10M, 2G.\n");
    print_usage(stderr);
    exit(EXIT_FAILURE);
}


int parse_args(RTSOpts * opts, int argc, char *argv[])
{
    if (argc == 0)
        return 0;

    if (strcmp(argv[0], "+RTS") != 0)
        return 0;

    int i;
    for (i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-RTS") == 0) {
            return i + 1;
        }

        if (argv[i][0] != '-') {
            fprintf(stderr, "RTS options should start with '-'.\n");
            print_usage(stderr);
            exit(EXIT_FAILURE);
        }

        switch (argv[i][1])
        {
        case '?':
            print_usage(stdout);
            exit(EXIT_SUCCESS);
            break;

        case 's':
            opts->show_summary = 1;
            break;

        case 'H':
            opts->init_heap_size = read_size(argv[i] + 2);
            break;

        case 'K':
            opts->max_stack_size = read_size(argv[i] + 2);
            break;

        default:
            printf("RTS opts: Wrong argument: %s\n", argv[i]);
            print_usage(stderr);
            exit(EXIT_FAILURE);
        }
    }

    return argc;
}

void parse_shift_args(RTSOpts * opts, int * argc, char *** argv) {
    size_t shift = parse_args(opts, (*argc) - 1, (*argv) + 1);

    char *prg = (*argv)[0];
    *argc = *argc - shift;
    *argv = *argv + shift;
    (*argv)[0] = prg;
}
