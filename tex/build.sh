#! /bin/sh

ott -tex_wrap false -i common.ott -i surface.ott -i core.ott -i translation.ott -o surface.ott.tex -tex_filter paper.mng paper.tex
xelatex paper.tex
bibtex paper.aux
xelatex paper.tex
xelatex paper.tex
exit 0
