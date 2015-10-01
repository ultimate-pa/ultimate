/**
 * 
 */
package jayhorn.soot;

import jayhorn.cfg.Program;
import jayhorn.soot.SootRunner.CallgraphAlgorithm;
import jayhorn.soot.util.MethodInfo;
import jayhorn.soot.util.SootTranslationHelpers;
import jayhorn.soot.visitors.SootStmtSwitch;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;

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
		SootPreprocessing.v().initialize();

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
//			Log.info("\t" + sm.getBytecodeSignature());
			SootTranslationHelpers.v().setCurrentMethod(sm);

			Body body = sm.retrieveActiveBody();
			processMethodBody(body);
		}
	}

	private void processMethodBody(Body body) {
//		System.err.println(body.toString());
		MethodInfo mi = new MethodInfo(body.getMethod(), SootTranslationHelpers.v().getCurrentSourceFileName());

		SootPreprocessing.v().removeAssertionRelatedNonsense(body);
		SootPreprocessing.v().reconstructJavaAssertions(body);

		SootStmtSwitch ss = new SootStmtSwitch(body, mi);
		mi.setSource(ss.getEntryBlock());

		mi.finalizeAndAddToProgram();
//		System.err.println(mi.getMethod());
	}
}
