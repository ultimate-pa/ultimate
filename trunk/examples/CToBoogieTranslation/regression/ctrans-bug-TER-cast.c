/*

2017-11-18 DD

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CTranslationTest.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-32bit-Automizer_Default.epf \
-i ../../../trunk/examples/svcomp/seq-mthreaded/rekh_aso_false-unreach-call.2.M1.c \
--cacsl2boogietranslator.entry.function main \
--core.toolchain.timeout.in.seconds 30 \
--deltadebugger.look.for.result.of.type TypeErrorResult \
--deltadebugger.result.long.description.prefix "Type mismatch (int != real)"

*/

int ud_err_theta  ;

void balance_init( )
{

  ud_err_theta = .0f;

}

