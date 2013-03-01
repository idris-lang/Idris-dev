
check: .PHONY
	$(IDRIS) --build effects.ipkg

recheck: clean check

install: 
	$(IDRIS) --install effects.ipkg

clean: .PHONY
	$(IDRIS) --clean effects.ipkg

.PHONY:
