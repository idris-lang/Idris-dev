check: .PHONY
	rm -f *.ibc
	for x in *.idr ; do \
	echo "Checking $$x"; \
	idris --check $$x; \
	done
	
.PHONY:
