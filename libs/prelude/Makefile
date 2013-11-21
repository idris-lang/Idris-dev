IDRIS := idris

build: .PHONY
	$(IDRIS) --build prelude.ipkg

install: 
	$(IDRIS) --install prelude.ipkg

clean: .PHONY
	$(IDRIS) --clean prelude.ipkg

rebuild: clean build

linecount: .PHONY
	find . -name '*.idr' | xargs wc -l

.PHONY:
