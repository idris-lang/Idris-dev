SRCS = prelude.idr list.idr nat.idr prelude.idr vect.idr

check: .PHONY
	for x in *.idr ; do \
	echo "Checking $$x"; \
	miniidris --noprelude --check $$x; \
	done

.PHONY:
