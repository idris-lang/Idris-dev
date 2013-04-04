
check: .PHONY
	$(IDRIS) --dynamicrts $(RTS) --build base.ipkg

recheck: clean check

install: 
	$(IDRIS) --dynamicrts $(RTS) --install base.ipkg

clean: .PHONY
	$(IDRIS) --dynamicrts $(RTS) --clean base.ipkg

linecount: .PHONY
	wc -l *.idr Network/*.idr Language/*.idr Prelude/*.idr Data/*.idr Control/Monad/*.idr Control/*.idr

.PHONY:
