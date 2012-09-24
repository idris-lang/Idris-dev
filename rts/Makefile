OBJS = idris_rts.o idris_gc.o idris_gmp.o idris_stdfgn.o
HDRS = idris_rts.h idris_gc.h idris_gmp.h idris_stdfgn.h
CFLAGS = -O2 -Wall -Werror

LIBTARGET = libidris_rts.a

check : $(LIBTARGET)

$(LIBTARGET) : $(OBJS)
	ar r $(LIBTARGET) $(OBJS)
	ranlib $(LIBTARGET)

install : .PHONY
	mkdir -p $(TARGET)
	install $(LIBTARGET) $(HDRS) $(TARGET)

clean : .PHONY
	rm -f $(OBJS) $(LIBTARGET)

idris_rts.o: idris_rts.h

.PHONY:
