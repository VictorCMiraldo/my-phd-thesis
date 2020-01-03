## The LaTeX command to use; it is a good idea to make
## sure you can specify the output-directory to be 'dist';
## it helps keeping the whole development organized.
LATEX=xelatex -shell-escape -output-directory=dist
## LATEX=latexmk -lualatex -auxdir=dist


## The target name and full name (with extension)
TGT=thesis
TGT_FULL=$(TGT).lhs

## The literate Haskell files that should go through
## lhs2TeX. Names are relative to src/
##
## It is generally a good idea to have only the
## toplevel file through lhs2TeX and use the '%include'
## directive internally.
BUILD_DEPENDS_LHS=$(TGT_FULL)

## Now, this very file might depend on other lhs files too,
## which should NOT go through lhs2TeX separatly
LHS_DEPENDENCIES=*.lhs

## Process the above list into a desired format.
## Example: if $(BUILD_DEPENDS_LHS) == "a.lhs b.lhs"
## then $(BUILD_DEPENDS_LHS_TEX) == "a.tex b.tex"
BUILD_DEPENDS_LHS_TEX=$(BUILD_DEPENDS_LHS:.lhs=.tex)

## The tex files that $(TGT) depends on. Relative to src/
## that were generated by lhs2TeX as well as those
## inside src/
BUILD_DEPENDS_TEX=

## Final list of files that the thesis depends on
BUILD_DEPENDS=$(addprefix src/,$(BUILD_DEPENDS_TEX)) \
              $(addprefix dist/,$(BUILD_DEPENDS_LHS_TEX))

## If your main file is an lhs file, the main file
## will be the corresponding tex file in dist.
## If your main file is a tex file, it should be
## the actual file in src.
MAIN_FILE=dist/$(TGT).tex
## MAIN_FILE=src/$(TGT).tex

## Build all necessary tex files with lhs2TeX
dist/%.tex: src/%.lhs $(addprefix src/,$(LHS_DEPENDENCIES))
	@mkdir -p dist
	lhs2TeX -o $@ $<

## Builds the target.
default : $(BUILD_DEPENDS) tex/latex/uustthesis.cls
	@mkdir -p dist
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) $(MAIN_FILE)

## Builds the index
index: 
	makeindex -s tex/latex/index_style.ist dist/thesis.idx 

## forces rebuild for bibliography.
dist/$(TGT).aux: default

mock: $(BUILD_DEPENDS) tex/latex/uustthesis.cls
	./mock-chapter
	lhs2TeX -o dist/mock-chapter.tex dist/mock-chapter.lhs
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) dist/mock-chapter.tex
	
remock: $(BUILD_DEPENDS) tex/latex/uustthesis.cls
	lhs2TeX -o dist/mock-chapter.tex dist/mock-chapter.lhs
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) dist/mock-chapter.tex
	
cover: cover/cover.svg default
	$(MAKE) -C cover/
	pdftk cover/frontcover.pdf dist/thesis.pdf cat output dist/with-cover.pdf

## Runs bibtex and builds the target with bibliography.
bib: references.bib dist/$(TGT).aux
	bibtex dist/$(TGT).aux
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) $(MAIN_FILE)

## Standard cleanup
clean:
	cd dist && rm -rf * && cd ..

## Install target for Nix
nix-install: default
	cp -r dist/*  ${out}


## Installs the math fonts locally
## Unfortunately, this is necessary for
## loading mathfonts, even with XeTeX.
fonts:
	@mkdir -p ~/.fonts
	cp tex/latex/fonts/* ~/.fonts/

## Runs a font-check on the generated pdf.
pdf-font-check: dist/$(TGT).pdf
	pdffonts dist/$(TGT).pdf
