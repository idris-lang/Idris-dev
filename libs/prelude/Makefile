IDRIS ?= idris
PKG   := prelude

build:
	$(IDRIS) --build ${PKG}.ipkg

install:
	$(IDRIS) --install ${PKG}.ipkg
	${IDRIS} --installdoc ${PKG}.ipkg

clean:
	$(IDRIS) --clean ${PKG}.ipkg

rebuild: clean build

linecount:
	find . -name '*.idr' | xargs wc -l

doc:
	$(IDRIS) --mkdoc ${PKG}.ipkg

doc_clean:
	rm -rf ${PKG}_doc

.PHONY: build install clean rebuild linecount doc
