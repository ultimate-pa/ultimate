//#Safe
/*
2017-11-24  DD

Example for 
de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator: AssertionError: cannot convert from CArray: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler.convertToPointer(CHandler.java:3073)


java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CheckedCTranslation.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-32bit-Automizer_Default.epf \
-i ../../../trunk/examples/svcomp/ntdrivers/floppy_true-unreach-call_true-valid-memsafety.i.cil.c \
--cacsl2boogietranslator.entry.function main \
--core.toolchain.timeout.in.seconds 30 \
--deltadebugger.ignore.reduction.with.results.of.type SyntaxErrorResult \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "AssertionError: cannot convert from CArray" 

*/ 

void main() {
  int *p = malloc(sizeof(int));
  memcpy(p, "", 1);
}

