include ../config.mk

OBJS = idris_rts.o idris_heap.o idris_gc.o idris_gmp.o idris_stdfgn.o idris_bitstring.o idris_opts.o idris_stats.o
HDRS = idris_rts.h idris_heap.h idris_gc.h idris_gmp.h idris_stdfgn.h idris_bitstring.h idris_opts.h idris_stats.h
CFLAGS = -O2 -Wall -fPIC

ifneq ($(GMP_INCLUDE_DIR),)
  CFLAGS += -isystem $(GMP_INCLUDE_DIR)
endif

LIBTARGET = libidris_rts.a
DYLIBTARGET = libidris_rts$(SHLIB_SUFFIX)

check : $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET) : $(OBJS)
	ar r $(LIBTARGET) $(OBJS)
	ranlib $(LIBTARGET)

$(DYLIBTARGET) : $(OBJS)
	$(CC) $(CFLAGS) -shared -o $(DYLIBTARGET) $(OBJS)

build: $(DYLIBTARGET)
	mkdir -p $(DIST)/rts
	install $(DYLIBTARGET) $(DIST)/rts


install : .PHONY
	mkdir -p $(TARGET)
	install $(LIBTARGET) $(DYLIBTARGET) $(HDRS) $(TARGET)

clean : .PHONY
	rm -f $(OBJS) $(LIBTARGET) $(DYLIBTARGET)

idris_rts.o: idris_rts.h

.PHONY:
