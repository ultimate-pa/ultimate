/*
DD 2017-11-18 

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CTranslationTest.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/float-benchs/water_pid_true-unreach-call_true-termination.c \
--cacsl2boogietranslator.entry.function main \
--core.toolchain.timeout.in.seconds 30 \
--deltadebugger.look.for.result.of.type TypeErrorResult \
--deltadebugger.result.long.description.prefix "Type mismatch (~NUM != bv32)"


*/
typedef double NUM;

NUM y( )
{

  return 0;
}

