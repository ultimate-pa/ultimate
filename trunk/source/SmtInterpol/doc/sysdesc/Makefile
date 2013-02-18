BASE ?= sysdesc

VIEWER ?= okular

ALL: $(BASE).pdf

VIEW: $(BASE).pdf
	$(VIEWER) $< &

%.pdf: %.tex $(wildcard *.bib)
	( pdflatex $(basename $<) || exit 1; \
	bibtex $(basename $<) || exit 1; \
	pdflatex $(basename $<) || exit 1; \
	latex_count=5 ; \
	while egrep -s \
	  'Rerun (LaTeX|to get cross-references right)' $(basename $<).log && \
	  [ $$latex_count -gt 0 ] ;\
	  do \
	    echo "Rerunning latex...." ;\
	    pdflatex $(basename $<) || exit 1; \
	    latex_count=`expr $$latex_count - 1` ;\
	  done ) || ( rm -f $@; exit 1 )

%.eps: %.fig
	fig2dev -L eps $< $@

.PHONY: ALL VIEW
