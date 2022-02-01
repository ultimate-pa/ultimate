/*
2017-11-15 Daniel Dietsch

Example for C Translation bug
de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator: NullPointerException: null: java.util.ArrayDeque.<init>(ArrayDeque.java:212)

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/AutomizerC_WitnessPrinter.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/ddv-machzwd/ddv_machzwd_outb_p_true-unreach-call_false-valid-memtrack.i \
--cacsl2boogietranslator.entry.function main \
--cacsl2boogietranslator.memory.model HoenickeLindenmann_8ByteResolution \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "NullPointerException: null"

*/

typedef unsigned int __u32;

struct watchdog_info {
 __u32 options;
};

void main(  )
{

 switch(0){
  case           sizeof(struct watchdog_info)          ? 0 : 0         :
	break;
 }

}
