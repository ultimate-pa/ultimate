/*
2017-11-15 Daniel Dietsch 

Example for C Translation bug 

de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator: UnsupportedOperationException: missing case?

Calling Ultimate with: 
java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/AutomizerC_WitnessPrinter.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-08_1a-drivers--net--xen-netback--xen-netback.ko-entry_point_false-unreach-call.cil.out.c \
--cacsl2boogietranslator.entry.function main \
--cacsl2boogietranslator.memory.model HoenickeLindenmann_8ByteResolution \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "UnsupportedOperationException: missing case?"

*/

typedef unsigned short u16;

struct xenvif_stat {
   int name  ;
   u16 offset ;
};

static struct xenvif_stat  const  xenvif_stats[1]   ;

void xenvif_get_strings(          )
{

  switch (0) {

  ldv_49049:
  memcpy(0,     & xenvif_stats[0].name ,
           0);

  }

}

