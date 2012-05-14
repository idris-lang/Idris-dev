OBJS = closure.o
HDRS = closure.h
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

closure.o: closure.h

.PHONY:
