
check: .PHONY
	$(IDRIS) --noprelude --verbose --check checkall.idr

recheck: clean check

install: check
	mkdir -p $(TARGET)/prelude
	mkdir -p $(TARGET)/network
	mkdir -p $(TARGET)/control/monad
	install *.ibc $(TARGET)
	install prelude/*.ibc $(TARGET)/prelude
	install network/*.ibc $(TARGET)/network
	install control/monad/*.ibc $(TARGET)/control/monad

clean: .PHONY
	rm -f *.ibc
	rm -f prelude/*.ibc
	rm -f network/*.ibc
	rm -f control/monad/*.ibc

linecount: .PHONY
	wc -l *.idr network/*.idr prelude/*.idr control/monad/*.idr

.PHONY:
