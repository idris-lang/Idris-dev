IDRIS     := idris

build:
	$(IDRIS) --build neweffects.ipkg

clean:
	$(IDRIS) --clean neweffects.ipkg

install:
	$(IDRIS) --install neweffects.ipkg

rebuild: clean build

.PHONY: build clean install rebuild
