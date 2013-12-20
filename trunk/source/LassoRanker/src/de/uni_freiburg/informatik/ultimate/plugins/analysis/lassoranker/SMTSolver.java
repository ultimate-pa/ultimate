package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;


/**
 * Create a new SMT solver script instance.
 * This solver needs to support non-linear algebraic constraint solving
 * ('QF_NRA').
 * 
 * @author Jan Leike
 */
class SMTSolver {
	
	/**
	 * Create a new SMT solver instance by calling an external z3 binary
	 */
	static Script newScript(String smt_solver_command,
			boolean produce_unsat_cores) {
		Logger solverLogger = Logger.getLogger("interpolLogger");
		Script script = new Scriptor(smt_solver_command, solverLogger);
		initScript(script, produce_unsat_cores);
		return script;
	}
	
	/**
	 * Reset an SMT script so that it forgets everything that happend
	 */
	static void resetScript(Script script, boolean produce_unsat_cores) {
		script.reset();
		initScript(script, produce_unsat_cores);
	}
	
	private static void initScript(Script script, boolean produce_unsat_cores) {
		if (produce_unsat_cores) {
			script.setOption(":produce-unsat-cores", true);
		}
		script.setOption(":produce-models", true);
		script.setLogic("QF_NRA"); // non-linear algebraic constraint solving
	}
}