build:
	$(MAKE) -C prelude build
	$(MAKE) -C base build
	$(MAKE) -C effects build
	$(MAKE) -C neweffects build
	$(MAKE) -C javascript build


install:
	$(MAKE) -C prelude install
	$(MAKE) -C base install
	$(MAKE) -C effects install
	$(MAKE) -C neweffects install
	$(MAKE) -C javascript install

clean:
	$(MAKE) -C prelude clean
	$(MAKE) -C base clean
	$(MAKE) -C effects clean
	$(MAKE) -C neweffects clean
	$(MAKE) -C javascript clean
        
.PHONY: build install clean
