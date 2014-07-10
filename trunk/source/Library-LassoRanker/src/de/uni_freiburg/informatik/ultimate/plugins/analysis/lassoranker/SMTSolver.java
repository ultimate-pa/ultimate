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

import java.io.File;
import java.io.FileNotFoundException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;


/**
 * Static class that manages SMT-Solver related things.
 * 
 * @author Jan Leike
 */
public class SMTSolver {
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	 * Auxiliary String that we put into the smt script via an echo.
	 * This String should help to identify the difficult constraints in a bunch
	 * of dumped smt2 files.
	 */
	public static String s_SolverUnknownMessage = 
			"Warning solver responded UNKNOWN to the check-sat above";
	
	/**
	 * Create a new SMT solver instance.
	 * If useExternalSolver is true, we use the Scriptor to start the external 
	 * SMT solver with the smt_solver_command.
	 * If useExternalSolver is false, we use SMTInterpol.
	 * 
	 * @param useExternalSolver
	 * @param smt_solver_command
	 * @param dump_filename name of the file the script should be dumped to,
	 *        can be null
	 * @param produce_unsat_cores produce unsat cores?
	 * @return the new script
	 */
	private static Script newScript(boolean useExternalSolver,
			String smt_solver_command,
			String dump_filename,
			boolean produce_unsat_cores) {
		Logger solverLogger = UltimateServices.getInstance()
				.getLoggerForExternalTool("constraintLogger");
		
		Script script; 
		if (useExternalSolver) {
			script = new Scriptor(smt_solver_command, solverLogger);
		} else {
			int timeoutMilliseconds = 1099 * 1000; 
			script = new SMTInterpol(solverLogger);
			script.setOption(":timeout", String.valueOf(timeoutMilliseconds));
		}
		
		// Dump script to file
		if (dump_filename != null) {
			try {
				script = new LoggingScript(script, dump_filename, true);
			} catch (FileNotFoundException e) {
				s_Logger.warn("Could not dump SMT script to file '"
						+ dump_filename + "': " + e);
			}
		}
		
		// Set options
		script.setOption(":produce-models", true);
		if (produce_unsat_cores) {
			script.setOption(":produce-unsat-cores", true);
		}
		return script;
	}
	
	/**
	 * Create a new solver instance with the preferences given
	 * @param preferences the preferences for creating the solver
	 * @param constraintsName name of the constraints whose satisfiability is
	 * checked
	 * @return the new solver instance
	 */
	public static Script newScript(Preferences preferences, String constraintsName) {
		return newScript(preferences.externalSolver,
				preferences.smt_solver_command,
				preferences.dumpSmtSolverScript ?
						composeFullFilename(preferences.path_of_dumped_script, 
								preferences.baseNameOfDumpedScript, 
								constraintsName) : null,
				preferences.annotate_terms);
	}
	
	/**
	 * Compose the full filename (of the dumped script) from 
	 * name of a path, baseNamePrefix of the file, name of the constraints,
	 * and the file ending ".smt2".
	 */
	public static String composeFullFilename(String path, String baseNamePrefix, 
			String constraintsName) {
		return path + File.separator + baseNamePrefix + "_" 
			+ constraintsName + ".smt2";
	}
	
	/**
	 * Define a new constant
	 * @param script SMT Solver
	 * @param name name of the new constant
	 * @param sort the sort of the variable
	 * @return the new variable as a term
	 * @throws SMTLIBException if something goes wrong, e.g. the name is
	 *          already defined
	 */
	public static Term newConstant(Script script, String name, String sortname)
			throws SMTLIBException {
		script.declareFun(name, new Sort[0], script.sort(sortname));
		return script.term(name);
	}
}