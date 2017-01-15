IDRIS?=idris

check:
	rm -f *.ibc
	for x in *.idr ; do \
	echo "Checking $$x"; \
	${IDRIS} --check $$x; \
	done

clean:
	rm -f *.ibc

.PHONY: check
