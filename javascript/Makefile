
check: .PHONY
	$(IDRIS) --build javascript.ipkg

recheck: clean check

install:
	$(IDRIS) --install javascript.ipkg

clean: .PHONY
	$(IDRIS) --clean javascript.ipkg

.PHONY:
