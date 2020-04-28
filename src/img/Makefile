all: runtimes-stdiff.pdf runtimes-hdiff.pdf

%.pdf: %.svg
	inkscape -z -d 400 -A $@ $<

# Attempting to convert to cmyk and preserve bounding box; this is really
# nasty.
#
#	gs -sDEVICE=pdfwrite -dNOPROMPT -dBATCH -dNOPAUSE \
#	  -sColorConversionStrategy=CMYK -dPDFSETTINGS=/prepress \
#	  -sOutputFile=$(@:.pdf=.aux) $@
#	echo "%PDF-1.7" > $@.bbox.aux
#	gs -dNOPAUSE -dBATCH -q -sDEVICE=bbox $@ 2>> $@.bbox.aux
#	tail -n+2 $(@:.pdf=.aux) | cat $@.bbox.aux - > $(@:.pdf=.cmyk.pdf)
	

