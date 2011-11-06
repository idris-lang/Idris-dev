SRCS = prelude.idr list.idr nat.idr prelude.idr vect.idr

check: .PHONY
	for x in *.idr ; do \
	echo "Checking $$x"; \
	idris --noprelude --check $$x; \
	done

.PHONY:
