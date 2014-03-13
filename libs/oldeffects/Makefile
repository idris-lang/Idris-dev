IDRIS     := idris

build:
	$(IDRIS) --build oldeffects.ipkg

clean:
	$(IDRIS) --clean oldeffects.ipkg

install:
	$(IDRIS) --install oldeffects.ipkg

rebuild: clean build

.PHONY: build clean install rebuild
