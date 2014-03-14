/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
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
	 * Create a new SMT solver instance.
	 * If useExternalSolver is true, we use the Scriptor to start the external 
	 * SMT solver with the smt_solver_command.
	 * If useExternalSolver is false, we use SMTInterpol.
	 */
	static Script newScript(boolean useExternalSolver,
			String smt_solver_command,
			boolean produce_unsat_cores) {
		Logger solverLogger = UltimateServices.getInstance().getLoggerForExternalTool("constraintLogger");
		final Script script; 
		if (useExternalSolver) {
			script = new Scriptor(smt_solver_command, solverLogger);
		} else {
			script = new SMTInterpol(solverLogger);
		}
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
	}
}