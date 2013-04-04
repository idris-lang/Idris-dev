
check: .PHONY
	$(IDRIS) --dynamicrts $(RTS) --build effects.ipkg

recheck: clean check

install: 
	$(IDRIS) --dynamicrts $(RTS) --install effects.ipkg

clean: .PHONY
	$(IDRIS) --dynamicrts $(RTS) --clean effects.ipkg

.PHONY:
