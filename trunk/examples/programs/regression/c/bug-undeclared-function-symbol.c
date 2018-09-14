//#Safe
/*
2017-11-21 DD

Minimal example for "SMTLIBException: Undeclared function symbol (v_~bitwiseOr_154)"

Stacktrace and log snippet 
--
[2017-11-21 20:08:54,974 INFO  L371      AbstractCegarLoop]: === Iteration 7 === [ldv_assert_linux_kernel_locking_spinlock__one_thread_double_lockErr0AssertViolation, ldv_assert_linux_kernel_locking_spinlock__one_thread_double_unlockErr0
AssertViolation, ldv_assert_linux_kernel_locking_spinlock__one_thread_locked_at_exitErr0AssertViolation]===
[2017-11-21 20:08:54,974 INFO  L82        PathProgramCache]: Analyzing trace with hash 1603406598, now seen corresponding path program 1 times
[2017-11-21 20:08:54,974 INFO  L208   onRefinementStrategy]: Switched to mode SMTINTERPOL_TREE_INTERPOLANTS
[2017-11-21 20:08:54,974 INFO  L91    tionRefinementEngine]: Using refinement strategy CamelRefinementStrategy
[2017-11-21 20:08:54,976 INFO  L101   rtionOrderModulation]: Keeping assertion order NOT_INCREMENTALLY
[2017-11-21 20:08:55,056 INFO  L136    AnnotateAndAsserter]: Conjunction of SSA is unsat
[2017-11-21 20:08:55,059 WARN  L137   erpolLogProxyWrapper]: Using partial proofs (cut at CNF-level).  Set option :produce-proofs to true to get complete proofs.
[2017-11-21 20:08:55,667 INFO  L134       CoverageAnalysis]: Checked inductivity of 65 backedges. 10 proven. 0 refuted. 0 times theorem prover too weak. 55 trivial. 0 not checked.
[2017-11-21 20:08:55,667 INFO  L372   tionRefinementEngine]: Constructing automaton from 1 perfect and 0 imperfect interpolant sequences.
[2017-11-21 20:08:55,667 INFO  L387   tionRefinementEngine]: Number of different interpolants: perfect sequences [5] imperfect sequences [] total 5
[2017-11-21 20:08:55,668 INFO  L409      AbstractCegarLoop]: Interpolant automaton has 5 states
[2017-11-21 20:08:55,668 INFO  L132   InterpolantAutomaton]: Constructing interpolant automaton starting with 5 interpolants.
[2017-11-21 20:08:55,668 INFO  L133   InterpolantAutomaton]: CoverageRelationStatistics Valid=7, Invalid=13, Unknown=0, NotChecked=0, Total=20
[2017-11-21 20:08:55,668 INFO  L87              Difference]: Start difference. First operand 3748 states and 4506 transitions. Second operand 5 states.
[2017-11-21 20:08:56,393 INFO  L142   InterpolantAutomaton]: Switched to read-only mode: deterministic interpolant automaton has 5 states.
[2017-11-21 20:08:56,394 FATAL L265        ToolchainWalker]: An unrecoverable error occured during an interaction with an SMT solver:
de.uni_freiburg.informatik.ultimate.logic.SMTLIBException: Undeclared function symbol (v_~bitwiseOr_154)
        at de.uni_freiburg.informatik.ultimate.logic.NoopScript.term(NoopScript.java:321)
        at de.uni_freiburg.informatik.ultimate.logic.NoopScript.term(NoopScript.java:296)
        at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.termVariable2constant(SmtUtils.java:708)
        at de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker.renameAuxVarsToCorrespondingConstants(IncrementalHoareTripleChecker.java:736)
        at de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker.assertCodeBlock(IncrementalHoareTripleChecker.java:387)
        at de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker.prepareAssertionStackAndAddTransition(IncrementalHoareTripleChecker.java:177)
        at de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker.checkReturn(IncrementalHoareTripleChecker.java:141)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ProtectiveHoareTripleChecker.checkReturn(ProtectiveHoareTripleChecker.java:80)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EfficientHoareTripleChecker.checkReturn(EfficientHoareTripleChecker.java:98)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker.checkReturn(CachingHoareTripleChecker.java:142)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton$ReturnSuccessorComputationHelper.computeSuccWithSolver(AbstractInterpolantAutomaton.java:444)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.BasicAbstractInterpolantAutomaton.chooseFalseSuccessor2(BasicAbstractInterpolantAutomaton.java:106)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.BasicAbstractInterpolantAutomaton.computeSuccs(BasicAbstractInterpolantAutomaton.java:72)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.BasicAbstractInterpolantAutomaton.computeSuccs(BasicAbstractInterpolantAutomaton.java:1)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton.returnSuccessors(AbstractInterpolantAutomaton.java:280)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton.returnSuccessors(AbstractInterpolantAutomaton.java:1)
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa.returnSuccessors(TotalizeNwa.java:308)
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ComplementDeterministicNwa.returnSuccessors(ComplementDeterministicNwa.java:142)
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ProductNwa.returnSuccessors(ProductNwa.java:284)
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ProductNwa.returnSuccessorsGivenHier(ProductNwa.java:308)
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates$ReachableStatesComputation.addReturnsAndSuccessors(NestedWordAutomatonReachableStates.java:1112)
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates$ReachableStatesComputation.<init>(NestedWordAutomatonReachableStates.java:946)
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates.<init>(NestedWordAutomatonReachableStates.java:185)
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference.computeDifference(Difference.java:137)
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference.<init>(Difference.java:90)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.computeAutomataDifference(BasicCegarLoop.java:548)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.refineAbstraction(BasicCegarLoop.java:518)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.iterateInternal(AbstractCegarLoop.java:420)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.iterate(AbstractCegarLoop.java:316)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.iterate(TraceAbstractionStarter.java:292)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.runCegarLoops(TraceAbstractionStarter.java:147)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.<init>(TraceAbstractionStarter.java:111)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionObserver.finish(TraceAbstractionObserver.java:117)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.runObserver(PluginConnector.java:168)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.runTool(PluginConnector.java:151)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.run(PluginConnector.java:128)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.executePluginConnector(ToolchainWalker.java:232)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.processPlugin(ToolchainWalker.java:226)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.walkUnprotected(ToolchainWalker.java:142)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.walk(ToolchainWalker.java:104)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainManager$Toolchain.processToolchain(ToolchainManager.java:324)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob.runToolchainDefault(DefaultToolchainJob.java:221)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob.run(BasicToolchainJob.java:134)
        at org.eclipse.core.internal.jobs.Worker.run(Worker.java:55)
--

java -Dosgi.configuration.area=./data/config -Xmx12G -Xms1G -jar ./plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar -data ./data \
-tc ../../../trunk/examples/toolchains/AutomizerC.xml \
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-64bit-Automizer_Default.epf \
-i ../../../trunk/examples/svcomp/ldv-challenges/linux-3.14__linux-kernel-locking-spinlock__drivers-net-ethernet-ti-tlan_true-unreach-call.cil.c \
--cacsl2boogietranslator.entry.function main \
--core.toolchain.timeout.in.seconds 10 \
--deltadebugger.look.for.result.of.type ExceptionOrErrorResult \
--deltadebugger.result.short.description.prefix "SMTLIBException: Undeclared function symbol" 



*/ 

struct net_device_ops {

   int (*ndo_stop)(  ) ;

};

struct net_device {

   struct net_device_ops  const  *netdev_ops ;

};

void ldv_check_final_state( ) ;

void ldv_assume(  ) ;
void ldv_stop( ) ;

void outb_p(int value , int port )
{

}

void ldv_unregister_netdev_74(  ) ;

int tlan_have_eisa  ;

void tlan_reset_adapter(  ) ;

void tlan_stop(int *dev )
{

  tlan_reset_adapter(dev);

  if (0) ; else ;

}

void tlan_eisa_cleanup( )
{
  int *dev ;

  goto ldv_43677;
  ldv_43676:

  ldv_unregister_netdev_74(dev);

  ldv_43677:
  if (tlan_have_eisa    ) {
    goto ldv_43676;
  } else ;

}
void tlan_exit( )
{

  if (1) {

    tlan_eisa_cleanup();

  } else ;

}

int tlan_close(int  dev )
{

  tlan_stop(0);

  if (0) ; else ;
  return 0;

}

void tlan_reset_adapter(int *dev )
{

  outb_p(     (unsigned int )0 | 0 , 0);

}

void ldv_unregister_netdev_stop_11_2(      ) ;

void ldv_EMGentry_exit_tlan_exit_14_2(int ( arg0)( ) )
{

  tlan_exit();

}

void ldv_entry_EMGentry_14(int  arg0 )
{

  if (0) ; else {

    ldv_assume( );
    ldv_EMGentry_exit_tlan_exit_14_2(0);
    ldv_check_final_state();
    ldv_stop();

  }

}
void main( )
{

  ldv_entry_EMGentry_14(0);

}

void ldv_unregister_netdev(int  arg0 , int  arg1 )
{
  struct net_device *ldv_11_netdev_net_device ;

  ldv_unregister_netdev_stop_11_2( ldv_11_netdev_net_device->netdev_ops ->ndo_stop,
                                  ldv_11_netdev_net_device);

}
void ldv_unregister_netdev_stop_11_2(int ( arg0)(  ) , int *arg1 )
{

  tlan_close(0);

}

void ldv_unregister_netdev_74(int *ldv_func_arg1 )
{

  ldv_unregister_netdev(0, 0);

}

void ldv_assert_linux_kernel_locking_spinlock__one_thread_locked_at_exit(int expr ) ;
int ldv_spin__xmit_lock_of_netdev_queue  =    1;

int ldv_spin_addr_list_lock_of_net_device  =    1;

void ldv_check_final_state( )
{

  ldv_assert_linux_kernel_locking_spinlock__one_thread_locked_at_exit(ldv_spin__xmit_lock_of_netdev_queue == 1);
  ldv_assert_linux_kernel_locking_spinlock__one_thread_locked_at_exit(ldv_spin_addr_list_lock_of_net_device == 1);

}

void ldv_assert_linux_kernel_locking_spinlock__one_thread_locked_at_exit(int expr )
{

  if (! expr) {

    __VERIFIER_error();

  } else ;

}

