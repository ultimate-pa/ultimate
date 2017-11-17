/*
DD 2017-11-17

java -Dosgi.configuration.area=./data/config -Xmx6G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CheckedCTranslationTest.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/seq-pthread/cs_fib_longer_true-unreach-call.i \
--cacsl2boogietranslator.entry.function main \
--core.toolchain.timeout.in.seconds 30 \
--cacsl2boogietranslator.memory.model HoenickeLindenmann_8ByteResolution \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "IllegalArgumentException: RValues cannot have array type" 

*/
union __CS__u {
 int i ;
 int j[1];
};
union __CS__u __CS_u;

void  t2( )
{

 __CS_u.j       ;

}

