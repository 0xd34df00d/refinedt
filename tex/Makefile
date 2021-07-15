OTTFILES = common.ott surface.ott core.ott translation.ott

full: paper.tex biblio.bib
	-pdflatex -shell-escape paper.tex
	-bibtex paper.aux
	-pdflatex -shell-escape paper.tex
	-pdflatex -shell-escape paper.tex

fast: paper.tex biblio.bib
	-pdflatex -shell-escape paper.tex
	-bibtex paper.aux

paper.tex: paper.mng $(OTTFILES)
	ott -tex_wrap false $(patsubst %, -i %, $(OTTFILES)) -o surface.ott.tex -tex_filter paper.mng paper.tex

clean:
	rm -f paper.tex paper.aux paper.pdf paper.log paper.bbl paper.blg surface.ott.tex paper.out

.PHONY: clean
