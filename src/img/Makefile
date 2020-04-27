all: runtimes-stdiff.pdf runtimes-hdiff.pdf

%.pdf: %.svg
	inkscape -z -d 400 -A $@ $<
