PAPER = idris-tutorial

all: ${PAPER}.pdf

TEXFILES = ${PAPER}.tex intro.tex starting.tex miscellany.tex typesfuns.tex

DIAGS = 

SOURCES = ${TEXFILES} ${DIAGS} macros.ltx library.ltx literature.bib

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

progress: .PHONY
	wc -w ${TEXFILES}

%.png : %.diag
	$(DITAA) -o -E $<

todropbox: .PHONY
	cp ${SOURCES} ~/Dropbox/TeX/idris-tutorial

fromdropbox: .PHONY
	cp ~/Dropbox/TeX/idris-tutorial/* .

.PHONY:
