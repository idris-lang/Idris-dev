OBJS = testidr.o
CFLAGS = `epic -includedirs` 

LIBTARGET = libidris.a

check: $(OBJS)
	ar -r $(LIBTARGET) $(OBJS)

install: check
	install $(LIBTARGET) $(TARGET)

.PHONY:
