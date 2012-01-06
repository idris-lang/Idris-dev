
check: .PHONY
	for x in *.idr ; do \
	echo "Checking $$x"; \
	idris --noprelude --check $$x; \
	done
	for x in network/*.idr ; do \
	echo "Checking $$x"; \
	idris --noprelude --check $$x; \
	done

recheck: clean check

install: recheck
	mkdir -p $(TARGET)/prelude
	mkdir -p $(TARGET)/network
	install *.ibc $(TARGET)
	install prelude/*.ibc $(TARGET)/prelude
	install network/*.ibc $(TARGET)/network

clean: .PHONY
	rm -f *.ibc
	rm -f prelude/*.ibc
	rm -f network/*.ibc

.PHONY:
