OBJS = idris_rts.o
HDRS = idris_rts.h
CFLAGS = -g

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
