#! /bin/sh

set -e

ott -tex_wrap false -i surface.ott -o surface.ott.tex
pdflatex paper.tex && bibtex paper.aux && pdflatex paper.tex && pdflatex paper.tex
