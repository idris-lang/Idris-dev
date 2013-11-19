include ../config.mk

OBJS = idris_rts.o idris_heap.o idris_gc.o idris_gmp.o idris_stdfgn.o \
       idris_bitstring.o idris_opts.o idris_stats.o
HDRS = idris_rts.h idris_heap.h idris_gc.h idris_gmp.h idris_stdfgn.h \
       idris_bitstring.h idris_opts.h idris_stats.h
CFLAGS:=-fPIC $(CFLAGS)
CFLAGS += $(GMP_INCLUDE_DIR)

LIBTARGET = libidris_rts.a

build: $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET) : $(OBJS)
	ar r $(LIBTARGET) $(OBJS)
	ranlib $(LIBTARGET)

install : .PHONY
	mkdir -p $(TARGET)
	install $(LIBTARGET) $(HDRS) $(TARGET)

clean : .PHONY
	rm -f $(OBJS) $(LIBTARGET) $(DYLIBTARGET)

idris_rts.o: idris_rts.h

.PHONY:
