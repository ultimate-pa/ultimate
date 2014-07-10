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
import java.io.Serializable;


/**
 * Global preferences for LassoRanker.
 * These values are constant for the lifetime of the LassoAnalysis object
 * 
 * This class functions much like a struct and is implemented like one.
 * 
 * @author Jan Leike
 */
public class LassoRankerPreferences implements Serializable {
	private static final long serialVersionUID = 3253589986886574198L;

	/**
	 * Should the polyhedra for stem and loop be made integral for integer
	 * programs?
	 * (Not yet implemented.)
	 */
	public boolean compute_integral_hull = false; // Default: false
	
	/**
	 * Add annotations to terms for debugging purposes
	 */
	public boolean annotate_terms = false; // Default: false
	
	/**
	 * If true, we use an external tool to solve the constraints. If false,
	 * we use SMTInterpol to solve the constraints. 
	 */
	public boolean externalSolver = true; // Default: true
	
	/**
	 * What shell command should be used to call the external smt solver?
	 */
	public String smt_solver_command = "z3 -smt2 -in SMTLIB2_COMPLIANT=true ";
	
	/**
	 * Write SMT solver script to file.
	 */
	public boolean dumpSmtSolverScript = false; // Default: false
	
	/**
	 * Path to which the SMT solver script is written.
	 */
	public String path_of_dumped_script = "."; // Default: "."
	
	/**
	 * Base name (without path) of the file to which the SMT solver script is 
	 * written.
	 */
	public String baseNameOfDumpedScript = "LassoRankerScript";

	/**
	 * Overapproximate the result of RewriteArrays by dropping all conjuncts
	 * that are not-equals relations of indices.
	 * If the lasso does not contain arrays, this option has no effect.
	 * Otherwise setting this to true is unsound for nontermination analysis.
	 */
	public boolean overapproximateArrayIndexConnection = false;
	
	/**
	 * Default construction intializes default values
	 */
	public LassoRankerPreferences() {
	}
	
	/**
	 * Copy constructor copies everything
	 */
	public LassoRankerPreferences(LassoRankerPreferences other) {
		this.compute_integral_hull = other.compute_integral_hull;
		this.annotate_terms = other.annotate_terms;
		this.externalSolver = other.externalSolver;
		this.smt_solver_command = other.smt_solver_command;
		this.dumpSmtSolverScript = other.dumpSmtSolverScript;
		this.path_of_dumped_script = other.path_of_dumped_script;
		this.baseNameOfDumpedScript = other.baseNameOfDumpedScript;
		this.overapproximateArrayIndexConnection =
				other.overapproximateArrayIndexConnection;
	}
	
	/**
	 * Verify that the settings are self-consistent and sane.
	 * Only makes assertion calls.
	 */
	public void checkSanity() {
		assert smt_solver_command != null;
		assert path_of_dumped_script != null;
		File f = new File(path_of_dumped_script);
		assert f.exists();
		assert f.isDirectory();
		assert baseNameOfDumpedScript != null;
	}
	
	/**
	 * Build a string description of the current preferences
	 */
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Compute integeral hull: ");
		sb.append(this.compute_integral_hull);
		sb.append("\nTerm annotations enabled: ");
		sb.append(this.annotate_terms);
		sb.append("\nUse exernal solver: ");
		sb.append(this.externalSolver);
		sb.append("\nSMT solver command: ");
		sb.append(this.smt_solver_command);
		sb.append("\nDump SMT script to file: ");
		sb.append(this.dumpSmtSolverScript);
		sb.append("\nPath of dumped script: ");
		sb.append(this.path_of_dumped_script);
		sb.append("\nFilename of dumped script: ");
		sb.append(this.baseNameOfDumpedScript);
		return sb.toString();
	}
}