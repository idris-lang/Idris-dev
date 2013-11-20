IDRIS := idris

build: .PHONY
	$(IDRIS) --build javascript.ipkg

install:
	$(IDRIS) --install javascript.ipkg

clean: .PHONY
	$(IDRIS) --clean javascript.ipkg

rebuild: clean build

.PHONY:
