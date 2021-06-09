project=main

all:$(project).pdf

LATEXMK := $(shell command -v latexmk 2> /dev/null)

.PHONY: all clean $(project) $(project).pdf

$(project): $(project).pdf

$(project).pdf: $(project).tex
ifndef LATEXMK
	xelatex -synctex=1 $(project).tex
	xelatex -synctex=1 $(project).tex
	bibtex $(project)
	xelatex -synctex=1 $(project).tex
else
	"latexmk" -pdf -xelatex -synctex=1 $(project).tex
endif

clean:
	rm -rf *.out *.dvi *.log *.out *.aux $(project).pdf *.bbl *.blg *.fdb_latexmk *.glo *.glsdefs *.ist *.synctex *.thm *.toc *.tdo *.fls
