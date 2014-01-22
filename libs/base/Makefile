IDRIS := idris

build:
	$(IDRIS) --build base.ipkg

install: 
	$(IDRIS) --install base.ipkg

clean:
	$(IDRIS) --clean base.ipkg

rebuild: clean build

linecount:
	find . -name '*.idr' | xargs wc -l

.PHONY: build install clean rebuild linecount
