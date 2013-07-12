package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.io.FileNotFoundException;
import java.text.SimpleDateFormat;
import java.util.Calendar;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;


/**
 * Create a new SMT solver script instance.
 * This solver needs to support non-linear algebraic constraint solving
 * ('QF_NRA').
 * 
 * @author Jan Leike
 */
class SMTSolver {
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private static String generateFilename() {
		String date = new SimpleDateFormat("yyyyMMdd_HHmmss").format(
				Calendar.getInstance().getTime());
		return "LassoRanker_" + date + ".smt2";
	}
	
	/**
	 * Create a new SMT solver instance by calling an external z3 binary
	 */
	static Script newScript() {
		// This code is copied from 
		// de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder
		
		Logger solverLogger = Logger.getLogger("interpolLogger");
		Script script = new Scriptor("z3 -smt2 -in", solverLogger);
		
		// Accesses the RCFGBuilder preferences for solver settings.
		TAPreferences taPref = new TAPreferences();
		if (taPref.dumpScript()) {
			String dumpFileName = taPref.dumpPath();
			String fileSep = System.getProperty("file.separator");
			dumpFileName += (dumpFileName.endsWith(fileSep) ? "" : fileSep);
			dumpFileName += generateFilename();
			s_Logger.info("Using temporary smt2 file '" + dumpFileName + "'.");
			try {
				script = new LoggingScript(script, dumpFileName, true);
			} catch (FileNotFoundException e) {
				throw new AssertionError(e);
			}
		}
		
		if (Preferences.annotate_terms) {
			script.setOption(":produce-unsat-cores", true);
		}
		script.setOption(":produce-models", true);
		script.setLogic("QF_NRA"); // non-linear algebraic constraint solving
		return script;
	}
}