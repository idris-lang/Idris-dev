
check: .PHONY
	$(IDRIS) --build base.ipkg

recheck: clean check

install: check
	$(IDRIS) --install base.ipkg

clean: .PHONY
	$(IDRIS) --clean base.ipkg

linecount: .PHONY
	wc -l *.idr network/*.idr language/*.idr prelude/*.idr control/monad/*.idr

.PHONY:
