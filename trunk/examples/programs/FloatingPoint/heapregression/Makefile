# This makefile allows to compile and run every regression test located in this
# directory.

#targets := $(subst ./,,$(basename $(shell find . -maxdepth 1 -regex '.*\.c' ! -name 'c-compile.c')))
sources := $(wildcard *.c)
targets := $(subst c-compile,,$(subst .c,,$(sources)))
objects := $(patsubst %.c, %.o, $(sources))

all : $(targets)

$(targets) : $(objects)
	gcc -o $@ $(addsuffix .o,$@) c-compile.o

$(objects) : $(sources)
	gcc -c $(sources)

clean :
	rm -f $(targets) $(addsuffix .o, $(targets)) c-compile.o

test : $(targets)
	@for file in $(targets); do \
		echo Running $$file ...; \
		./$$file; \
		if [ $$? -ne 0 ]; then \
			exit; \
		fi; \
		echo; \
	done

.PHONY: all source clean test
