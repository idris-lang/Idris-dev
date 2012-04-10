OBJS = network.o testidr.o
HDRS = network.h testidr.h

CFLAGS = `epic -includedirs` 

LIBTARGET = libidris.a

check: $(OBJS)
	ar -r $(LIBTARGET) $(OBJS)

install: check
	install $(LIBTARGET) $(TARGET)
	install $(HDRS) $(TARGET)

.PHONY:
