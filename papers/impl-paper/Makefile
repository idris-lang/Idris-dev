PAPER = impldtp

all: ${PAPER}.pdf

TEXFILES = ${PAPER}.tex intro.tex conclusions.tex hll.tex\
           typechecking.tex elaboration.tex delab.tex \
	   syntax.tex

DIAGS = 

SOURCES = ${TEXFILES} ${DIAGS} macros.ltx library.bib

DITAA = java -jar ~/Downloads/ditaa.jar

${PAPER}.pdf: ${SOURCES}
#	dvipdf ${PAPER}.dvi
	pdflatex ${PAPER}
	-bibtex ${PAPER}
	-pdflatex ${PAPER}
	-pdflatex ${PAPER}

${PAPER}.ps: ${PAPER}.dvi
	dvips -o ${PAPER}.ps ${PAPER}

${PAPER}.dvi: $(SOURCES)
	-latex ${PAPER}
	-bibtex ${PAPER}
	-latex ${PAPER}
	-latex ${PAPER}

progress:
	wc -w ${TEXFILES}

%.png : %.diag
	$(DITAA) -o -E $<

todropbox:
	cp ${SOURCES} ~/Dropbox/TeX/ImplDTP/

fromdropbox:
	cp ~/Dropbox/TeX/ImplDTP/* .

.PHONY: all progress todropbox fromdropbox
