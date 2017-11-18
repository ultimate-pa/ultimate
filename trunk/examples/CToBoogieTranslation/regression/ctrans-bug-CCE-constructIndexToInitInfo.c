/*

2017-11-18 DD

26 examples
de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator: ClassCastException: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray cannot be cast to de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InitializationHandlerInitializerInfo.constructIndexToInitInfo(InitializationHandler.java:1087)

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CheckedCTranslation.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/ddv-machzwd/ddv_machzwd_outl_true-unreach-call_false-valid-memtrack.i \
--cacsl2boogietranslator.entry.function main \
--cacsl2boogietranslator.memory.model HoenickeLindenmann_8ByteResolution \
--core.toolchain.timeout.in.seconds 10 \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.long.description.prefix "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator: ClassCastException: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray cannot be cast to de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct" 


*/

struct watchdog_info {

 int identity[1];
};

static struct watchdog_info zf_info = {
 .identity = "ZF-Logic watchdog",
};

void zf_ioctl(  )
{

 switch(0){
            zf_info     ;

}

}

