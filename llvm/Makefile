include ../config.mk

CFLAGS=-c -O2 -Wall -Wextra -fPIC -Wno-unused-parameter
SOURCES=defs.c
OBJECTS=$(SOURCES:.c=.o)
LIB=libidris_rts.a

all: $(SOURCES) $(LIB)

$(LIB): $(OBJECTS) 
	ar r $@ $(OBJECTS)
	ranlib $@

.c.o:
	$(CC) $(CFLAGS) $< -o $@

install: $(LIB) .PHONY
	mkdir -p $(TARGET)
	install $(LIB) $(TARGET)

clean: .PHONY
	rm -f $(OBJECTS) $(LIB)

.PHONY:
