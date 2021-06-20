filename=main

pdf: ps
	ps2pdf ${filename}.ps

ps:	dvi
	dvips -t letter ${filename}.dvi

dvi:
	pdflatex -synctex=1 -interaction=nonstopmode ${filename}
	bibtex ${filename}||true
	pdflatex -synctex=1 -interaction=nonstopmode ${filename}
	pdflatex -synctex=1 -interaction=nonstopmode ${filename}

quick:
	pdflatex -synctex=1 -interaction=nonstopmode ${filename}

read:
	pkill -x Skim
	open -a Skim ${filename}.pdf &

clean:
	rm -f ${filename}.{ps,pdf,log,aux,out,dvi,bbl,blg}