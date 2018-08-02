# Thesis Template for Software Technology at Utrecht University

This repo contains a class file (`tex/latex/uustthesis.cls`) 
together with a example build set-up for writing larger
LaTeX documents. 

If you are just looking for the class file and needs no help
in setting it up, just take `tex/latex/uustthesis.cls`.

If you want the whole package, the best option is to fork
or clone this repo and use it for your thesis. 

# Structure of the Repo

  - User created files go under `src/`
  - Everything that is generated by tools goes into `dist/`
    and is ignored by git.
  - Packages that you might want to include manually go into
    `tex/latex/`
  - Documentation on how to write and/or customize class files
    can be found under `doc/`. If you are writing a MSc thesis,
    please, stick to minimal customization.
  
## Configuring the Makefile

  We use GNU `make` to build our pdf. The makefile provided here
requires minimal configuration to build a pdf. Make sure that
the following variables are correctly set:

  1. `TGT` is the name of the target *without* extensions.
  2. `TGT_FULL` is the name of the target *with* extneions.
  3. `BUILD_DEPENDS_LHS` is the list of files that should be
      processed by `lhs2TeX`. In most cases, this will be just
      the topmost file. This list contains filenames relative
      to `src/`
  4. `BUILD_DEPENDS_TEX` is the list of LaTeX files that are
     required to build the pdf. This list contains filenames
     relative to `src/`
  5. `MAIN_FILE` should be either `dist/$(TGT).tex` or
     `src/$(TGT).tex`. This depends on whether or not the main
     LaTeX file was generated by `lhs2TeX` or not.