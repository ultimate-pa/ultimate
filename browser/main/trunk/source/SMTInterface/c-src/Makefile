WORKSPACEDIR ?= /home/juergen/work/stalin/source
X86Z3HOME ?= /home/juergen/smtsolver/z3-32bit
X86_64Z3HOME ?= /home/juergen/smtsolver/z3
CCACHE ?= /usr/bin/ccache
JAVA_INCLUDE_DIR ?= /usr/lib/jvm/java/include
EXTRADEFS?=

DISTDIR32 = $(WORKSPACEDIR)/SMTInterface.linux.x86/libs
DISTDIR64 = $(WORKSPACEDIR)/SMTInterface.linux.x86_64/libs
# Force building a 32 bit library with 8kb got space on RISC-CPUs...
# Use memory debugging for now...
CXXFLAGS_common = -Wall -Wextra -fpic -DPIC \
	-I$(JAVA_INCLUDE_DIR) -I$(JAVA_INCLUDE_DIR)/linux \
	-D_FORTIFY_SOURCE=2 -fstack-protector \
	-fvisibility=hidden -fvisibility-inlines-hidden $(foreach def,$(EXTRADEFS),-D$(def))
CXXFLAGS_debug = -g
CXXFLAGS_release = -O2 -DNDEBUG
# Set runpath to $ORIGIN such that every dependant library is found in the
# same place as libnativez3.so
# TODO: Check need for -rdynamic...
LDFLAGS = -pie \
	 -shared -Wl,-rpath,'$$ORIGIN'
CXXFLAGS=$(CXXFLAGS_common) $(CXXFLAGS_debug)

SOURCES = $(wildcard *.cc)
HEADERS = $(wildcard *.hh)
EXTRADEPS_COMPILE = $(wildcard $(Z3HOME)/include/*.h) \
	$(JAVA_INCLUDE_DIR)/jni.h \
	$(JAVA_INCLUDE_DIR)/linux/jni_md.h

SOBJPREFIX32 = .sobj32
SOBJPREFIX64 = .sobj64

debug: CXXFLAGS=$(CXXFLAGS_common) $(CXXFLAGS_debug)
debug: $(SOBJPREFIX32)/libnativez3.so $(SOBJPREFIX64)/libnativez3.so

release: CXXFLAGS=$(CXXFLAGS_common) $(CXXFLAGS_release)
release: $(SOBJPREFIX32)/libnativez3.so $(SOBJPREFIX64)/libnativez3.so FORCE

${SOBJPREFIX32}/libnativez3.so: LDFLAGS+=-L$(X86Z3HOME)/lib -lz3-gmp -m32
${SOBJPREFIX32}/libnativez3.so: \
	$(addprefix $(SOBJPREFIX32)/,$(patsubst %.cc,%.o,$(SOURCES))) \
	$(X86Z3HOME)/lib/libz3-gmp.so
	$(CCACHE) $(LINK.o) $(filter-out $(X86Z3HOME)/lib/libz3-gmp.so,$^) -o $@

#This is almost the built-in rule with some more dependencies
${SOBJPREFIX32}/%.o: CXXFLAGS+=-m32 -I$(X86Z3HOME)/include
${SOBJPREFIX32}/%.o: %.cc ${EXTRADEPS_COMPILE}
	mkdir -p $(SOBJPREFIX32)
	$(CCACHE) $(COMPILE.cc) -o $@ $<

${SOBJPREFIX64}/libnativez3.so: LDFLAGS+=-L$(X86_64Z3HOME)/lib -lz3
${SOBJPREFIX64}/libnativez3.so: \
	$(addprefix $(SOBJPREFIX64)/,$(patsubst %.cc,%.o,$(SOURCES))) \
	$(X86_64Z3HOME)/lib/libz3.so
	$(CCACHE) $(LINK.o) $(filter-out $(X86_64Z3HOME)/lib/libz3.so,$^) -o $@

#This is almost the built-in rule with some more dependencies
${SOBJPREFIX64}/%.o: CXXFLAGS+=-I$(X86_64Z3HOME)/include
${SOBJPREFIX64}/%.o: %.cc ${EXTRADEPS_COMPILE}
	mkdir -p $(SOBJPREFIX64)
	$(CCACHE) $(COMPILE.cc) -o $@ $<


# Use in conjunction with debug or release!!!
dist:
	mkdir -p $(DISTDIR32)
	mkdir -p $(DISTDIR64)
	cp $(SOBJPREFIX32)/libnativez3.so $(X86Z3HOME)/lib/libz3-gmp.so $(DISTDIR32)
	cp $(SOBJPREFIX64)/libnativez3.so $(X86_64Z3HOME)/lib/libz3.so $(DISTDIR64)

clean:
	rm -rf $(SOBJPREFIX32) $(SOBJPREFIX64); rm -f *~

distclean: clean
	rm -f $(DISTDIR32)/libnativez3.so $(DESTDIR64)/libnativez3.so \
	$(DISTDIR32)/libz3-gmp.so $(DESTDIR64)/libz3.so

FORCE:

.PHONY: debug release dist clean distclean FORCE 
