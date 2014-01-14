include ../config.mk

CFLAGS:=-Wextra -fPIC -Wno-unused-parameter $(CFLAGS)
SOURCES=defs.c
OBJECTS=$(SOURCES:.c=.o)
LIB=libidris_rts.a

build: $(SOURCES) $(LIB)

$(LIB): $(OBJECTS) 
	ar r $@ $(OBJECTS)
	ranlib $@

.c.o:
	$(CC) -c $(CFLAGS) $< -o $@

install: $(LIB)
	mkdir -p $(TARGET)
	install $(LIB) $(TARGET)

clean:
	rm -f $(OBJECTS) $(LIB)

.PHONY: build install clean
