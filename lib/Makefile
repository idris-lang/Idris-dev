
check: .PHONY
	for x in *.idr ; do \
	echo "Checking $$x"; \
	idris --noprelude --check $$x; \
	done

recheck: clean check

install: check
	install *.ibc $(TARGET)
	mkdir -p $(TARGET)/prelude
	install prelude/*.ibc $(TARGET)/prelude

clean: .PHONY
	rm -f *.ibc
	rm -f prelude/*.ibc

.PHONY:
