#! /bin/sh

set -e

ott -tex_wrap false -i surface.ott -o surface.ott.tex
pdflatex paper.tex
