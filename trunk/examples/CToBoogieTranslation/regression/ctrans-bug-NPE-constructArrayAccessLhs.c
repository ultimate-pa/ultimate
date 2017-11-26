/*
2017-11-18 DD 

46 examples affected
de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator: NullPointerException: null: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil.constructArrayAccessLhs(CTranslationUtil.java:107)

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/CheckedCTranslation.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Bitvector.epf \
-i ../../../trunk/examples/svcomp/ldv-memsafety/StructInitialization1_true-valid-memsafety.c \
--cacsl2boogietranslator.entry.function main \
--cacsl2boogietranslator.memory.model HoenickeLindenmann_8ByteResolution \
--core.toolchain.timeout.in.seconds 10 \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.long.description.prefix "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator: NullPointerException: null: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil.constructArrayAccessLhs" 
*/

struct lockdep_map {

   int  class_cache[1] ;

};

struct raw_spinlock {
   int raw_lock ;

   struct lockdep_map dep_map ;
};

union __anonunion_ldv_6060_30 {
   struct raw_spinlock rlock ;

};

struct spinlock {
   union __anonunion_ldv_6060_30 ldv_6060 ;
};

typedef struct spinlock spinlock_t;

struct ratelimit_state {

   spinlock_t lock ;

};

        struct ratelimit_state drbd_ratelimit_state = { 1
                                     };

void main() {
        drbd_ratelimit_state.lock    ;

}

