#$Id:: Makefile 1338 2008-11-01 11:20:59Z jbaa004                            $:

LATEX = latex
TEX = tex
PS2PDF = ps2pdf
PDFLATEX = pdflatex
PDFTEX = pdftex
BIBTEX = bibtex
TEXFLAGS = --recorder
DVIPS = dvips
MPOST = mpost
MFLAGS = --recorder
BIBFLAGS = -terse
INPUTS := $(wildcard *.tex)
DVI := $(INPUTS:.tex=.dvi)
PS := $(INPUTS:.tex=.ps)
PDF := $(INPUTS:.tex=.pdf)
MPX := $(INPUTS:.tex=.mpx)
FLS := $(INPUTS:.tex=.fls)
BBL := $(INPUTS:.tex=.bbl)
BIB := $(INPUTS:.tex=.bib)
BLG := $(INPUTS:.tex=.blg)
AUX := $(INPUTS:.tex=.aux)

.PHONY: all clean

all: ideas.pdf design.pdf

$(MPX): %.mpx: %.mp
	$(MPOST) $(MFLAGS) $<

$(BIB): mgrp.bib
	ln -sf mgrp.bib $@

$(BBL): %.bbl: %.bib %.aux 
	$(BIBTEX) $(BIBFLAGS) $(basename $<)

$(AUX): %.aux: %.tex 
	$(LATEX) $(TEXFLAGS) $<
	$(LATEX) $(TEXFLAGS) $<

$(DVI): %.dvi: %.tex %.bbl 
	$(LATEX) $(TEXFLAGS) $<
	$(LATEX) $(TEXFLAGS) $<
	$(LATEX) $(TEXFLAGS) $<

$(PS): %.ps: %.dvi 
	$(DVIPS) -o $@ $<

#$(PDF): %.pdf: %.ps
#	$(PS2PDF) $<

$(PDF): %.pdf: %.tex %.bbl %.aux
	$(PDFLATEX) $(TEXFLAGS) $<
	$(PDFLATEX) $(TEXFLAGS) $<

clean:
	rm -f *~ `grep OUTPUT $(FLS) | cut -f 2 -d ' '` $(FLS) $(PS) $(PDF) $(BBL) $(BLG)
