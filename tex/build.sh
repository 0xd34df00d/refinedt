#! /bin/sh

set -e

ott -tex_wrap false -i common.ott -i surface.ott -i core.ott -o surface.ott.tex -tex_filter paper.mng paper.tex
pdflatex paper.tex && bibtex paper.aux && pdflatex paper.tex && pdflatex paper.tex
