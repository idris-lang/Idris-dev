LIBS=prelude base contrib effects pruviloj

build: $(LIBS:=.built)

doc: $(LIBS:=.doc)

install: $(LIBS:=.install)

clean: $(LIBS:=.clean)

doc_clean:
	rm -rf */*_doc *.doc

rebuild: clean build

linecount: $(LIBS:=.linecount)


%.built: %
	cd $< && $(IDRIS) --build $<.ipkg
	touch $@

%.clean: %
	cd $< && $(IDRIS) --clean $<.ipkg
	rm -f $<.built

%.install: % %.built %.doc
	cd $< && $(IDRIS) --install $<.ipkg && $(IDRIS) --installdoc $<.ipkg

%.doc: %
	cd $< && $(IDRIS) --mkdoc $<.ipkg
	touch $@

%.linecount: %
	cd $< && find . -name '*.idr' | xargs wc -l

base.built: prelude.built

contrib.built: prelude.built base.built

pruviloj.built: prelude.built base.built

effects.built: prelude.built base.built

.PHONY: build rebuild install clean doc doc_clean
