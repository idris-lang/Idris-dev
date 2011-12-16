
check: .PHONY
	for x in *.idr ; do \
	echo "Checking $$x"; \
	idris --noprelude --check $$x; \
	done

recheck: clean check

install: check
	mkdir -p $(TARGET)/prelude
	install *.ibc $(TARGET)
	install prelude/*.ibc $(TARGET)/prelude

clean: .PHONY
	rm -f *.ibc
	rm -f prelude/*.ibc

.PHONY:
