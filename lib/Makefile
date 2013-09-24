IDRIS := idris

build: .PHONY
	$(IDRIS) --build base.ipkg

install: 
	$(IDRIS) --install base.ipkg

clean: .PHONY
	$(IDRIS) --clean base.ipkg

rebuild: clean build

linecount: .PHONY
	find . -name '*.idr' | xargs wc -l

.PHONY:
