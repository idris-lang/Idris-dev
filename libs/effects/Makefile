IDRIS     := idris

build: .PHONY
	$(IDRIS) --build effects.ipkg

clean: .PHONY
	$(IDRIS) --clean effects.ipkg

install:
	$(IDRIS) --install effects.ipkg

rebuild: clean build

.PHONY:
