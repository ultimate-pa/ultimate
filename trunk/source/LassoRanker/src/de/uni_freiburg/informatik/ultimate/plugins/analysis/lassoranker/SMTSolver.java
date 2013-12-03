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
		// This code is copied from 
		// de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder
		
		Logger solverLogger = Logger.getLogger("interpolLogger");
		Script script = new Scriptor(smt_solver_command, solverLogger);
		
		if (produce_unsat_cores) {
			script.setOption(":produce-unsat-cores", true);
		}
		script.setOption(":produce-models", true);
		script.setLogic("QF_NRA"); // non-linear algebraic constraint solving
		return script;
	}
}