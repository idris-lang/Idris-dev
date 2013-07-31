include ../config.mk

PKG_CONFIG_CFLAGS:=$(shell (pkg-config --version >/dev/null 2>&1) && pkg-config --cflags bdw-gc)
CFLAGS:=-Wextra -fPIC -Wno-unused-parameter $(PKG_CONFIG_CFLAGS) $(CFLAGS)
SOURCES=defs.c
OBJECTS=$(SOURCES:.c=.o)
LIB=libidris_rts.a

build: $(SOURCES) $(LIB)

$(LIB): $(OBJECTS)
	ar r $@ $(OBJECTS)
	ranlib $@

.c.o:
	$(CC) -c $(CFLAGS) $< -o $@

install: $(LIB) .PHONY
	mkdir -p $(TARGET)
	install $(LIB) $(TARGET)

clean: .PHONY
	rm -f $(OBJECTS) $(LIB)

.PHONY:
