IDRIS := idris

build:
	$(IDRIS) --build prelude.ipkg

install: 
	$(IDRIS) --install prelude.ipkg

clean:
	$(IDRIS) --clean prelude.ipkg

rebuild: clean build

linecount:
	find . -name '*.idr' | xargs wc -l

.PHONY: build install clean rebuild linecount
