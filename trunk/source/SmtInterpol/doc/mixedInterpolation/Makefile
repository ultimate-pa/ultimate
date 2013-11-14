SHELL=/bin/bash

BASE_TR ?= techReport_mixedInterpolation
BASE_TC ?= tacas_mixedInterpolation
BASE_NTR ?= newtechreport

VIEWER ?= okular

all: $(BASE_TC).pdf $(BASE_TR).pdf $(BASE_NTR).pdf 

viewtr: $(BASE_TR).pdf
	$(VIEWER) $< 2>/dev/null &

viewtc: $(BASE_TC).pdf
	$(VIEWER) $< 2>/dev/null &

BIBS=$(wildcard *.bib)

TEXS=$(wildcard *.tex) $(wildcard *.cls) $(wildcard *.sty) iif-logo-en.pdf unifr-neu.pdf

%.pdf: %.tex $(TEXS) $(BIBS) Makefile
	( pdflatex -halt-on-error $(basename $<) || exit 1; \
	grep -q bibdata $(basename $<).aux && ( bibtex $(basename $<) || exit 1 ); \
	pdflatex -halt-on-error $(basename $<) || exit 1; \
	latex_count=5 ; \
	while egrep -s \
	  'Rerun (LaTeX|to get cross-references right)' $(basename $<).log && \
	  [ $$latex_count -gt 0 ] ;\
	  do \
	    echo "Rerunning latex...." ;\
	    pdflatex -halt-on-error $(basename $<) || exit 1; \
	    latex_count=`expr $$latex_count - 1` ;\
	  done ) || ( rm -f $@; exit 1 )

%.eps: %.fig
	fig2dev -L eps $< $@

clean:
	GLOBIGNORE=*.pdf:*.bib:*.tex:*.sty:*.cls && rm -f $(BASE_TR).* $(BASE_TC).* *~

RELEASEZIP: $(BASE_TC).pdf
	GLOBIGNORE=$(BASE_TR).tex && zip $(BASE_TC)-sources.zip $(TEXS) $(BIBS) Makefile $(BASE_TC).pdf

.PHONY: all view_tc view_tr clean RELEASEZIP
