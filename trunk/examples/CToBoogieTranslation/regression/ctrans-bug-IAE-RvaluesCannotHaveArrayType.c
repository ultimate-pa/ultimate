/*
2017-11-18 DD

13 examples affected 
de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator: IllegalArgumentException: RValues cannot have array type: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue.checkType(RValue.java:85)

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CheckedCTranslation.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-43_2a-drivers--net--ethernet--intel--ixgbe--ixgbe.ko-entry_point_true-unreach-call.cil.out.c \
--cacsl2boogietranslator.entry.function main \
--cacsl2boogietranslator.memory.model HoenickeLindenmann_8ByteResolution \
--core.toolchain.timeout.in.seconds 10 \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "IllegalArgumentException: RValues cannot have array type" 

*/ 

struct __anonstruct_formatted_403 {

   int flow_type ;

};
union ixgbe_atr_input {
   struct __anonstruct_formatted_403 formatted ;
   int dword_stream[1] ;
};

void ixgbe_add_ethtool_fdir_entry(      )
{

  union ixgbe_atr_input mask ;

  mask.formatted.flow_type = 0;

}

