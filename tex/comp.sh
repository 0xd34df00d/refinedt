#! /bin/sh

set -e

ott -tex_wrap false -i common.ott -i surface.ott -i core.ott -i translation.ott -o surface.ott.tex -tex_filter paper.mng paper.tex
pdflatex -shell-escape paper.tex
bibtex paper.aux
