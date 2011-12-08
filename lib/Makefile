
check: .PHONY
	for x in *.idr ; do \
	echo "Checking $$x"; \
	idris --noprelude --check $$x; \
	done

recheck: clean check

clean: .PHONY
	rm -f *.ibc
	rm -f prelude/*.ibc

.PHONY:
