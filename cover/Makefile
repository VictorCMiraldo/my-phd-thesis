SOURCES=$(wildcard *.svg)
TARGETS=$(SOURCES:.svg=.pdf)

all: cover.pdf frontcover.pdf bookmark.pdf

cover.pdf: cover.svg
	inkscape -A cover.pdf cover.svg

bookmark.pdf: bookmark.svg
	inkscape -A bookmark.pdf bookmark.svg

frontcover.pdf: frontcover.tex cover.pdf
	pdflatex frontcover.tex
	pdftk frontcover.pdf cat 2 output res.pdf
	mv res.pdf frontcover.pdf
	rm *.aux *.log


