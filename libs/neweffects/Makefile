IDRIS     := idris

build:
	$(IDRIS) --build effects.ipkg

clean:
	$(IDRIS) --clean effects.ipkg

install:
	$(IDRIS) --install effects.ipkg

rebuild: clean build

.PHONY: build clean install rebuild
