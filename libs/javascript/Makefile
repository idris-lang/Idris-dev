IDRIS := idris

build:
	$(IDRIS) --build javascript.ipkg

install:
	$(IDRIS) --install javascript.ipkg

clean:
	$(IDRIS) --clean javascript.ipkg

rebuild: clean build

.PHONY: build install clean rebuild
