IDRIS := idris

build: .PHONY
	$(IDRIS) --build simpleparser.ipkg

install:
	$(IDRIS) --install simpleparser.ipkg

clean: .PHONY
	$(IDRIS) --clean simpleparser.ipkg

rebuild: clean build

.PHONY:
