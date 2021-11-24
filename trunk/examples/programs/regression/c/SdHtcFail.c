//#Safe
/*
    2021-09-14 Daniel Dietsch

    For branch wip/dd/seqcomp 5fbdf5bf49

    Started with
    $ /usr/bin/java -Dosgi.configuration.area=/storage/repos/ultimate/releaseScripts/default/UAutomizer-linux/data/config -Xmx15G -Xms4m -ea -jar /storage/repos/ultimate/releaseScripts/default/UAutomizer-linux/plugins/org.eclipse.equinox.launcher_1.5.800.v20200727-1323.jar -data @noDefault -ultimatedata /storage/repos/ultimate/releaseScripts/default/UAutomizer-linux/data -tc /storage/repos/ultimate/releaseScripts/default/UAutomizer-linux/config/AutomizerMemDerefMemtrack.xml -i ../sv-benchmarks/c/ldv-memsafety/memleaks_test13_2.i -s /storage/repos/ultimate/releaseScripts/default/UAutomizer-linux/config/svcomp-DerefFreeMemtrack-32bit-Automizer_Bitvector.epf --cacsl2boogietranslator.entry.function main --witnessprinter.witness.directory /storage/repos/ultimate/releaseScripts/default/UAutomizer-linux --deltadebugger.look.for.result.of.type "ExceptionOrErrorResult" --deltadebugger.result.long.description.prefix "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction: AssertionError: HoareTripleChecker results differ between SdHoareTripleChecker"
*/

void *ldv_malloc(int size) {
  return malloc(size);
}

struct ldv_list_head {
 int  next,  prev;
};

void ldv_list_del(int  entry)
{

}

struct ldv_list_head global_list_13  ;

void alloc_13( ) {
    ldv_malloc(0);
}

void free_unsafe_13() {

  ({ int  __mptr =  (&global_list_13)->next ;  });
  ldv_list_del(0);

}
void entry_point( ) {
 alloc_13();
 free_unsafe_13();
}
void main( ) {
     entry_point();
}

