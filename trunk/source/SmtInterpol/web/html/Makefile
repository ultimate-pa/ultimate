XMLFILES=$(wildcard *.xml)
DATE:=$(shell date)

all: $(addprefix gen/,$(subst .xml,.html,$(XMLFILES)))
	@find ..  -maxdepth 1 -type f | xargs cp -t gen

gen/navi.xml: file.lst $(XMLFILES) gennavi.xsl
	@mkdir -p gen
	@xsltproc -o $@ gennavi.xsl $<

gen/%.html: %.xml gen/navi.xml genpage.xsl
	@mkdir -p gen
	@xsltproc --stringparam date "${DATE}" -o $@ genpage.xsl $<

downloadpage:
	@svn info --xml https://sotec.informatik.uni-freiburg.de/svn/stalin/branch/quantifier > tmp.xml
	@xsltproc -o download.xml gendownloadpage.xsl tmp.xml
	@rm -f tmp.xml

distributable:
	$(if $(findstring undefined,$(origin FILES)), $(error "define variable FILES"))
	@mkdir -p gen
	$(foreach FILE,$(subst :, ,$(FILES)),( cp $(FILE) gen && cd gen && md5sum $(notdir $(FILE)) > $(notdir $(FILE)).md5 && sha256sum $(notdir $(FILE)) > $(notdir $(FILE)).sha );)

distribution:
	@$(MAKE) FILES=../../../smtinterpol.jar:../../../smtinterpol-src.zip distributable downloadpage
	@$(MAKE) all
	@echo "run scp SmtInterpol/web/html/gen/*.html SmtInterpol/web/html/gen/smtinterpol* <your destination>"

.PHONY: all distributable downloadpage distribution
