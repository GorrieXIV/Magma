#$Id:: Makefile 769 2008-08-28 04:54:13Z jbaa004                             $:

LATEX = latex
PS2PDF = ps2pdf
PDFTEX = pdflatex
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
BLG := $(INPUTS:.tex=.blg)
AUX := $(INPUTS:.tex=.aux)

.PHONY: all clean

all: hb.pdf

$(MPX): %.mpx: %.mp
	$(MPOST) $(MFLAGS) $<

$(BBL): %.bbl: %.bib %.aux 
	$(BIBTEX) $(BIBFLAGS) $(basename $<)

$(AUX): %.aux: %.tex
	$(LATEX) $(TEXFLAGS) $<

$(DVI): %.dvi: %.tex %.aux %.bbl
	$(LATEX) $(TEXFLAGS) $<
	$(LATEX) $(TEXFLAGS) $<

$(PS): %.ps: %.dvi %.tex
	$(DVIPS) -o $@ $<

#$(PDF): %.pdf: %.ps
#	$(PS2PDF) $<

$(PDF): %.pdf: %.tex %.bbl %.aux
	$(PDFTEX) $(TEXFLAGS) $<
	$(PDFTEX) $(TEXFLAGS) $<

clean:
	rm -f *~ `grep OUTPUT $(FLS) | cut -f 2 -d ' '` $(FLS) $(PS) $(PDF) $(BBL) $(BLG) $(DVI)
