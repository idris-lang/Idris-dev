
check: .PHONY
	$(IDRIS) --build base.ipkg

recheck: clean check

install: 
	$(IDRIS) --install base.ipkg

clean: .PHONY
	$(IDRIS) --clean base.ipkg

linecount: .PHONY
	wc -l *.idr Network/*.idr Language/*.idr Prelude/*.idr Control/Monad/*.idr

.PHONY:
