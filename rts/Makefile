include ../config.mk

OBJS = idris_rts.o idris_heap.o idris_gc.o idris_gmp.o idris_bitstring.o \
       idris_opts.o idris_stats.o idris_utf8.o idris_stdfgn.o \
       idris_buffer.o getline.o idris_net.o itoa.o
HDRS = idris_rts.h idris_heap.h idris_gc.h idris_gmp.h idris_bitstring.h \
       idris_opts.h idris_stats.h idris_stdfgn.h idris_net.h \
       idris_buffer.h idris_utf8.h getline.h itoa.h
CFLAGS := $(CFLAGS)
CFLAGS += $(GMP_INCLUDE_DIR) $(GMP) -DIDRIS_TARGET_OS="\"$(OS)\""
CFLAGS += -DIDRIS_TARGET_TRIPLE="\"$(MACHINE)\""

ifeq ($(OS), windows)
	OBJS += windows/win_utils.o
else
	CFLAGS += -fPIC
endif

ifdef BARE_METAL
	# Using this flag changes the precision of float casts compared to snprintf.
	# e.g. 2345.345 get converted to "2345.344970703125" instead of "234.345"
	OBJS += ftoa.o
	HDRS += ftoa.h
endif

ifndef IDRIS_GMP
	OBJS += mini-gmp.o
	HDRS += mini-gmp.h
endif

LIBTARGET = libidris_rts.a

build: $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET) : $(OBJS)
	$(AR) rc $(LIBTARGET) $(OBJS)
	$(RANLIB) $(LIBTARGET)

install :
	mkdir -p $(TARGET)
	install $(LIBTARGET) $(HDRS) $(TARGET)

clean :
	rm -f $(OBJS) $(LIBTARGET) $(DYLIBTARGET)

$(OBJS): $(HDRS)

.PHONY: build install clean
