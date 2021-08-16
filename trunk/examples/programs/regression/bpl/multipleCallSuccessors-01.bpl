//#Safe
/*
    20021-06-21 Daniel Dietsch
    
    Necessary setting:
    --traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg=true 
    
    java.lang.UnsupportedOperationException: State has more than one call successor
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates$AncestorComputation$1.next(NestedWordAutomatonReachableStates.java:1771)
        at de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates$AncestorComputation$1.next(NestedWordAutomatonReachableStates.java:1)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotationFragments.addDeadEndDoubleDeckers(HoareAnnotationFragments.java:288)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.computeAutomataDifference(BasicCegarLoop.java:908)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop.refineAbstraction(BasicCegarLoop.java:771)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.iterateInternal(AbstractCegarLoop.java:468)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.iterate(AbstractCegarLoop.java:372)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopUtils.getCegarLoopResult(CegarLoopUtils.java:69)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopUtils.getCegarLoopResult(CegarLoopUtils.java:63)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.executeCegarLoop(TraceAbstractionStarter.java:383)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.analyseProgram(TraceAbstractionStarter.java:317)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.analyseSequentialProgram(TraceAbstractionStarter.java:277)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.runCegarLoops(TraceAbstractionStarter.java:175)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.<init>(TraceAbstractionStarter.java:154)
        at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionObserver.finish(TraceAbstractionObserver.java:124)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.runObserver(PluginConnector.java:168)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.runTool(PluginConnector.java:151)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.run(PluginConnector.java:128)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.executePluginConnector(ToolchainWalker.java:232)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.processPlugin(ToolchainWalker.java:226)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.walkUnprotected(ToolchainWalker.java:142)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.walk(ToolchainWalker.java:104)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainManager$Toolchain.processToolchain(ToolchainManager.java:320)
        at de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.RerunFreshToolchainJob.run(RerunFreshToolchainJob.java:91)
        at org.eclipse.core.internal.jobs.Worker.run(Worker.java:63)
 */

var x : int;

procedure main()
modifies x;
{
  x:=0;
  if(*){
    call foo1();
  } else if  (*){
    call foo2();
  } else {
    assume false;
  }
  assert x == 1; 
}

procedure foo1()
modifies x;
{
  x:=x+1;
}

procedure foo2()
modifies x;
{
  x:=x+1;
}




