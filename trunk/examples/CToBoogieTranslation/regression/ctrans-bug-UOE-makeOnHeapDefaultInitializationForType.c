/*

DD 2017-11-16

The Plugin de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator has thrown an exception:
java.lang.UnsupportedOperationException: missing case?
        at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InitializationHandler.makeOnHeapDefaultInitializationForType(InitializationHandler.java:505)
        at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InitializationHandler.makeOnHeapDefaultInitializationForType(InitializationHandler.java:487)
        at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InitializationHandler.makeDefaultInitialization(InitializationHandler.java:450)

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CTranslationOnly.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/ldv-commit-tester/m0_true-unreach-call_drivers-media-radio-si4713-i2c-ko--111_1a--064368f.c \
--cacsl2boogietranslator.entry.function main \
--core.toolchain.timeout.in.seconds 30 \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "UnsupportedOperationException: missing case?" 

*/

typedef unsigned long kernel_ulong_t;

struct i2c_device_id {

   kernel_ulong_t driver_data ;
};

static struct i2c_device_id  const  si4713_id    ;

static struct i2c_driver si4713_i2c_driver  =
     {
        & si4713_id          };
void si4713_module_init( )
{

          si4713_i2c_driver ;

}

