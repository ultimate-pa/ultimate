/**
 * DD 2017-11-08
 * 
 * Use TC BuchiAutomizerCInline.xml and settings/default/automizer/svcomp-Termination-32bit-Automizer_Default.epf to trigger the following bug.
 *
 *   java.lang.AssertionError: stemTF is false but stem analysis said: feasible
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.computeStemTF(LassoCheck.java:545)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck$LassoCheckResult.<init>(LassoCheck.java:415)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.<init>(LassoCheck.java:300)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoop.iterate(BuchiCegarLoop.java:472)
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
 */ 
void main() {
  int i, j;
  int length  ;
   
  int fac  ;

    __builtin_alloca (fac*length  );
   
  for (i=0; i<1; i++) ;
  for (;  ;  ) ;
   
}