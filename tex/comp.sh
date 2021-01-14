#! /bin/sh

set -e

ott -tex_wrap false -i common.ott -i surface.ott -i core.ott -i translation.ott -o surface.ott.tex -tex_filter paper.mng paper.tex
bibtex paper.aux
xelatex -shell-escape paper.tex
