/** 
 * DD 2017-11-08
 * 
 * Use TC BuchiAutomizerCInline.xml and settings/default/automizer/svcomp-Termination-32bit-Automizer_Default.epf to trigger the following bug.
 *  java.lang.IndexOutOfBoundsException: Index: 1, Size: 1
 *  	at java.util.ArrayList.rangeCheck(ArrayList.java:653)
 *  	at java.util.ArrayList.get(ArrayList.java:429)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex.get(ArrayIndex.java:90)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminator.computeDoubletons(MapEliminator.java:772)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminator.<init>(MapEliminator.java:158)
 *  	at de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.MapEliminationLassoPreprocessor.process(MapEliminationLassoPreprocessor.java:99)
 *  	at de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoBuilder.applyPreprocessor(LassoBuilder.java:154)
 *  	at de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoBuilder.preprocess(LassoBuilder.java:262)
 *  	at de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.preprocess(LassoAnalysis.java:284)
 *  	at de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.<init>(LassoAnalysis.java:233)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.synthesize(LassoCheck.java:828)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.access$16(LassoCheck.java:755)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck$LassoCheckResult.checkLassoTermination(LassoCheck.java:508)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck$LassoCheckResult.<init>(LassoCheck.java:416)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.<init>(LassoCheck.java:300)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoop.iterate(BuchiCegarLoop.java:456)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerObserver.doTerminationAnalysis(BuchiAutomizerObserver.java:150)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerObserver.finish(BuchiAutomizerObserver.java:386)
 *  	at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.runObserver(PluginConnector.java:168)
 *  	at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.runTool(PluginConnector.java:151)
 *  	at de.uni_freiburg.informatik.ultimate.core.coreplugin.PluginConnector.run(PluginConnector.java:128)
 *  	at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.executePluginConnector(ToolchainWalker.java:232)
 *  	at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.processPlugin(ToolchainWalker.java:226)
 *  	at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.walkUnprotected(ToolchainWalker.java:142)
 *  	at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker.walk(ToolchainWalker.java:104)
 *  	at de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainManager$Toolchain.processToolchain(ToolchainManager.java:324)
 *  	at de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob.runToolchainDefault(DefaultToolchainJob.java:221)
 *  	at de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob.run(BasicToolchainJob.java:134)
 *  	at org.eclipse.core.internal.jobs.Worker.run(Worker.java:56)
 *
 *
 */

void main() {
  int i, j;
  int length  ;

  int *arr = alloca(length*sizeof(int));
   
  int value  ;
   
  for (i=0; i<length; i++) {
    arr[i] = value++;
  }
   
  while (1) {
    if (arr[1] > arr[    0]) {
      j++;
    } else ;
  }
   
}