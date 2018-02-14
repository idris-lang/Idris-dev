# Target
TARGETS := libsel4-idris-rts.a

# Source files required to build the target
FILES := \
    idris_rts.c \
    idris_heap.c \
    idris_gc.c \
    idris_gmp.c \
    idris_bitstring.c \
    idris_opts.c \
    idris_stats.c \
    idris_utf8.c \
    idris_stdfgn.c \
    mini-gmp.c \
    idris_buffer.c \
    getline.c \
    idris_net.c \
    seL4/idris_main.c
CFILES := $(addprefix rts/,$(FILES))

# Header file directory this library provides
HDRFILES := $(wildcard ${SOURCE_DIR}/rts/*)

CFLAGS += -W -Wall
# Don't use the host machines' environment when cross compiling
CFLAGS += -undef
CFLAGS += -DIDRIS_TARGET_OS=\"seL4\"
CFLAGS += -DSEL4
MACHINE := $(shell $(CC) -dumpmachine)
CFLAGS += -DIDRIS_TARGET_TRIPLE=\"$(MACHINE)\"

include $(SEL4_COMMON)/common.mk
