/*
2017-11-15 Daniel Dietsch

Example for C Translation bug

de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator: UnsupportedOperationException: missing case?

Calling Ultimate with:
java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/AutomizerC_WitnessPrinter.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/array-industry-pattern/array_of_struct_single_elem_init_true-unreach-call.i \
--cacsl2boogietranslator.entry.function main \
--cacsl2boogietranslator.memory.model HoenickeLindenmann_8ByteResolution \
--core.toolchain.timeout.in.seconds 10 \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "NullPointerException: null" \
--deltadebugger.result.long.description.prefix "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator: NullPointerException: null: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InitializationHandler$InitializerInfo.constructStructFieldInitInfos(InitializationHandler.java:911)" 
*/


struct S
{
 int p;
 int n;
};
struct S a[100000];

void main()
{

  struct S s1 = a[0]   ;

}
