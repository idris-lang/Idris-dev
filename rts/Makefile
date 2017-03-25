include ../config.mk

OBJS = idris_rts.o idris_heap.o idris_gc.o idris_gmp.o idris_bitstring.o \
       idris_opts.o idris_stats.o idris_utf8.o idris_stdfgn.o mini-gmp.o \
       idris_buffer.o getline.o
HDRS = idris_rts.h idris_heap.h idris_gc.h idris_gmp.h idris_bitstring.h \
       idris_opts.h idris_stats.h mini-gmp.h idris_stdfgn.h idris_net.h \
       idris_buffer.h idris_utf8.h getline.h
CFLAGS := $(CFLAGS)
CFLAGS += $(GMP_INCLUDE_DIR) $(GMP) -DIDRIS_TARGET_OS="\"$(OS)\""
CFLAGS += -DIDRIS_TARGET_TRIPLE="\"$(MACHINE)\""

# NOTE: This works around glibc 2.11 not declaring pthread_mutexattr_settype
# and PTHREAD_MUTEX_RECURSIVE by default, causing compilation failures on
# Debian 6 and Ubuntu 10.04 LTS.
ifeq ($(OS), unix)
ifneq ($(shell ldd --version | head -n 1 | grep 2.11),)
	CFLAGS += -D_GNU_SOURCE
endif
endif

ifeq ($(OS), windows)
	OBJS += windows/idris_net.o windows/win_utils.o
else
	CFLAGS += -fPIC
	OBJS += idris_net.o
endif

LIBTARGET = libidris_rts.a

build: $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET) : $(OBJS)
	$(AR) r $(LIBTARGET) $(OBJS)
	$(RANLIB) $(LIBTARGET)

install :
	mkdir -p $(TARGET)
	install $(LIBTARGET) $(HDRS) $(TARGET)

clean :
	rm -f $(OBJS) $(LIBTARGET) $(DYLIBTARGET)

idris_rts.o: idris_rts.h

.PHONY: build install clean
