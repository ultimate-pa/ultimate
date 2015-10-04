/**
 * 
 */
package soottocfg.soot;

import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.toolkits.annotation.nullcheck.NullnessAnalysis;
import soot.toolkits.graph.CompleteUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soottocfg.cfg.Program;
import soottocfg.soot.SootRunner.CallgraphAlgorithm;
import soottocfg.soot.transformers.AssertionReconstruction;
import soottocfg.soot.transformers.ExceptionTransformer;
import soottocfg.soot.transformers.SwitchStatementRemover;
import soottocfg.soot.util.MethodInfo;
import soottocfg.soot.util.SootTranslationHelpers;
import soottocfg.soot.visitors.SootStmtSwitch;

/**
 * This is the main class for the translation. It first invokes Soot to load all
 * classes and perform points-to analysis and then translates them into
 * Boogie/Horn.
 * 
 * @author schaef
 *
 */
public class SootToCfg {

	/**
	 * Run Soot and translate classes into Boogie/Horn
	 * 
	 * @param input
	 * @param classPath
	 * @param cfg
	 */
	public void run(String input, String classPath, CallgraphAlgorithm cfg) {

		// run soot to load all classes.
		SootRunner runner = new SootRunner();
		runner.run(input, classPath, cfg);
		// init the helper classes for pre-processing
		AssertionReconstruction.v().initialize();

		// Create a new program
		Program program = new Program();
		SootTranslationHelpers.v().setProgram(program);

		for (SootClass sc : Scene.v().getClasses()) {
			processSootClass(sc);
		}
		
		// now set the entry points.
		for (SootMethod entryPoint : Scene.v().getEntryPoints()) {
			if (entryPoint.getDeclaringClass().isApplicationClass()) {
				//TODO: maybe we want to add all Main methods instead.
				program.addEntryPoint(program.loopupMethod(entryPoint.getSignature()));
			}
		}
	}

	public Program getProgram() {
		return SootTranslationHelpers.v().getProgram();
	}

	/**
	 * Analyze a single SootClass and transform all its Methods
	 * 
	 * @param sc
	 */
	private void processSootClass(SootClass sc) {
		if (sc.resolvingLevel() < SootClass.SIGNATURES) {
			return;
		}

		if (sc.isApplicationClass()) {
//			Log.info("Class " + sc.getName() + "  " + sc.resolvingLevel());

			SootTranslationHelpers.v().setCurrentClass(sc);

			for (SootMethod sm : sc.getMethods()) {
				processSootMethod(sm);
			}
		}

	}

	private void processSootMethod(SootMethod sm) {
		if (sm.isConcrete()) {			
			//TODO
//			if (!sm.getSignature().equals("<org.apache.tools.ant.taskdefs.optional.unix.Symlink: void delete()>")) {
//				return;
//			}
//			System.err.println(sm.getSignature());
			
			SootTranslationHelpers.v().setCurrentMethod(sm);

			Body body = sm.retrieveActiveBody();
			processMethodBody(body);
		}
	}

	private void processMethodBody(Body body) {
		
//		System.err.println(body.toString());		
		preProcessBody(body);
//		System.err.println(body.toString());
		
		//generate the CFG structures on the processed body.
		MethodInfo mi = new MethodInfo(body.getMethod(), SootTranslationHelpers.v().getCurrentSourceFileName());
		SootStmtSwitch ss = new SootStmtSwitch(body, mi);
		mi.setSource(ss.getEntryBlock());

		mi.finalizeAndAddToProgram();
//		System.err.println(mi.getMethod());
	}
	
	private void preProcessBody(Body body) {
		//pre-process the body
		UnitGraph unitGraph = new CompleteUnitGraph(body);
		NullnessAnalysis localNullness = new NullnessAnalysis(unitGraph);
//		LocalMayAliasAnalysis localMayAlias = new LocalMayAliasAnalysis(unitGraph);
		
		//first reconstruct the assertions.
		AssertionReconstruction.v().removeAssertionRelatedNonsense(body);
		AssertionReconstruction.v().reconstructJavaAssertions(body);

		//make the exception handling explicit
		ExceptionTransformer em = new ExceptionTransformer(localNullness);
		em.transform(body);
		//replace all switches by sets of IfStmt
		SwitchStatementRemover so = new SwitchStatementRemover();
		so.transform(body);
		
	}
}
