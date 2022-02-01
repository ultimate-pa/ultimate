/*

2017-11-21 DD

Program leads to TypeError, affecting important benchmarks 

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CheckedCTranslation.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/ldv-challenges/linux-3.14__linux-kernel-locking-spinlock__drivers-net-ethernet-ti-tlan_true-unreach-call.cil.c \
--cacsl2boogietranslator.entry.function main \
--cacsl2boogietranslator.memory.model HoenickeLindenmann_4ByteResolution \
--core.toolchain.timeout.in.seconds 10 \
--deltadebugger.look.for.result.of.type TypeErrorResult \
--deltadebugger.result.long.description.prefix "Type mismatch (bv32 != bv8)" 

*/

void main()
{
  "" ;
}

