PAPER = impldtp

all: ${PAPER}.pdf .PHONY

TEXFILES = ${PAPER}.tex intro.tex conclusions.tex overview.tex hll.tex\
           typechecking.tex proofstate.tex elaboration.tex compiling.tex\
	   syntax.tex

DIAGS = 

SOURCES = ${TEXFILES} ${DIAGS} macros.ltx library.bib

library.bib: .PHONY
	cp ~/Research/Papers/library.bib .

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
	cp ${SOURCES} ~/Dropbox/TeX/ImplDTP/

fromdropbox: .PHONY
	cp ~/Dropbox/TeX/ImplDTP/* .

.PHONY:
