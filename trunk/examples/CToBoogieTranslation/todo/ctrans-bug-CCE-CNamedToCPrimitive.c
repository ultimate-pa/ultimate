/*

DD 2017-11-28

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CheckedCTranslation.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/ntdrivers/cdaudio_false-unreach-call.i.cil.c \
--cacsl2boogietranslator.entry.function main \
--core.toolchain.timeout.in.seconds 30 \
--deltadebugger.ignore.reduction.with.results.of.type "SyntaxErrorResult" \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "ClassCastException: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed cannot be cast to de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive" 
*/

typedef unsigned char UCHAR;

struct _CDB10 {

   UCHAR Reserved1 : 1 ;

};

union _CDB {

   struct _CDB10 CDB10 ;

};
typedef union _CDB *PCDB;

void CdAudio535DeviceControl(      )
{

  PCDB cdb ;

                        cdb->CDB10.Reserved1 = 0;

}

