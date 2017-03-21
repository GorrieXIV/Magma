#$Id:: Makefile 1150 2008-10-15 04:37:00Z jbaa004                            $:

SHELL=/bin/sh

INPUTR = prospect.R
INPUTM = prospect
export FIG_OUTPUT := mixing_quotients.eps
MATLAB_OPTS = -nosplash -nodesktop -nojvm -nodisplay
EPS = $(FIG_OUTPUT)

all: figures fixeps

figures:
#	R --vanilla --slave < $(INPUTR)
	matlab $(MATLAB_OPTS) -r $(INPUTM)

fixeps: $(PDF) $(EPS)

$(EPS): %.eps: %.bak.eps
	eps2eps $< $@
	rm $<

$(PDF): %.eps
	epstopdf $<

clean:
	rm -f $(EPS) $(PDF)
