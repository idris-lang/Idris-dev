build:
	$(MAKE) -C prelude build
	$(MAKE) -C base build
	$(MAKE) -C effects build


install:
	$(MAKE) -C prelude install
	$(MAKE) -C base install
	$(MAKE) -C effects install

clean:
	$(MAKE) -C prelude clean
	$(MAKE) -C base clean
	$(MAKE) -C effects clean

doc:
	$(MAKE)	-C prelude doc 	
	$(MAKE)	-C base doc 	
	$(MAKE)	-C effects doc 	

doc_clean:
	$(MAKE)	-C prelude doc_clean
	$(MAKE)	-C base doc_clean 	
	$(MAKE)	-C effects  doc_clean	


.PHONY: build install clean doc doc_clean
