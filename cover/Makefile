SOURCES=$(wildcard *.svg)
TARGETS=$(SOURCES:.svg=.pdf)

all: cover.pdf backcover.pdf frontcover.pdf bookmark.pdf

cover.pdf: cover.svg
	inkscape -d 300 -A cover.pdf cover.svg

bookmark.pdf: bookmark.svg
	inkscape -d 300 -A bookmark.pdf bookmark.svg

frontcover.pdf: frontcover.tex cover.pdf
	pdflatex frontcover.tex
	pdftk frontcover.pdf cat 2 output res.pdf
	mv res.pdf frontcover.pdf
	rm *.aux *.log

backcover.pdf: backcover.tex cover.pdf
	pdflatex backcover.tex
	pdftk backcover.pdf cat 2 output res.pdf
	mv res.pdf backcover.pdf
	rm *.aux *.log




