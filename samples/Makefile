check:
	rm -f *.ibc
	for x in *.idr ; do \
	echo "Checking $$x"; \
	idris -p effects --check $$x; \
	done

.PHONY: check
