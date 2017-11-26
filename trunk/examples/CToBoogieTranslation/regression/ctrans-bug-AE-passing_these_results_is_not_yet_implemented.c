/*

DD 2017-11-16

The Plugin de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator has thrown an exception:
java.lang.AssertionError: passing these results is not yet implemented
        at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler.visit(CHandler.java:1005)

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CTranslationOnly.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/ldv-linux-3.4-simple/32_1_cilled_true-unreach-call_ok_nondet_linux-3.4-32_1-drivers--media--dvb--frontends--it913x-fe.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c \
--cacsl2boogietranslator.entry.function main \
--core.toolchain.timeout.in.seconds 30 \
--cacsl2boogietranslator.memory.model HoenickeLindenmann_8ByteResolution \
--cacsl2boogietranslator.check.division.by.zero ASSERTandASSUME \
--cacsl2boogietranslator.check.division.by.zero.for.floating.types ASSERTandASSUME \
--cacsl2boogietranslator.check.unreachability.of.error.function.in.sv-comp.mode false \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "AssertionError: passing these results is not yet implemented" 

*/

struct cpumask {
   int bits[     0  /  0     ] ;
};

typedef struct cpumask  cpumask_var_t;

struct mm_struct {

   cpumask_var_t cpu_vm_mask_var ;

};

struct kiocb {

   struct kioctx  ki_ctx ;

};

struct kioctx {

   struct mm_struct  mm ;

};

struct address_space_operations {

   int ( direct_IO)(     struct kiocb
                          ) ;

};

struct address_space {

   struct address_space_operations  const   a_ops ;

} __attribute__((__aligned__(sizeof(long )))) ;

struct file {

   struct address_space  f_mapping ;

};

struct file_operations {

   int ( llseek)(struct file             ) ;

};

struct dvb_adapter {

   struct dvb_device  mfe_dvbdev ;

};
struct dvb_device {

   struct file_operations  const   fops ;

};

struct dvb_frontend {

   struct dvb_adapter  dvb ;

};

void it913x_fe_init(struct dvb_frontend  fe )
;

