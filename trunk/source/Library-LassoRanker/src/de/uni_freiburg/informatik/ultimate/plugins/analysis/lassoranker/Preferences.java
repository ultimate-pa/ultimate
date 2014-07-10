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

import java.io.Serializable;


/**
 * Accumulation of preferences for LassoRanker.
 * 
 * These are the preferences that you might want to change when using
 * LassoRanker as a library through the class LassoRankerTerminationAnalysis.
 * 
 * The prefences in the Ultimate GUI have some additional preferences that
 * are relevent when using LassoRanker as a standalone plugin in the toolchain.
 * 
 * This class functions much like a struct and is implemented like one.
 * 
 * @see PreferencesInitializer
 * @author Jan Leike
 */
public class Preferences implements Serializable {
	private static final long serialVersionUID = 3253589986886574198L;
	
	/**
	 * Enum for different types of termination and nontermination analysis
	 */
	public enum AnalysisType {
		/**
		 * Do not do any analysis (this is the fastest ^^).
		 */
		Disabled,
		
		/**
		 * Use only linear SMT solving. Fast but incomplete.
		 */
		Linear,
		
		/**
		 * Use linear SMT solving, but use a number of guesses for eigenvalues
		 * of the loop to retain more solution compared to plain linear SMT
		 * solving.
		 */
		Linear_with_guesses,
		
		/**
		 * Use nonlinear constraint solving.
		 * This is relatively complete but generally the slowest.
		 */
		Nonlinear;
		
		/**
		 * @return whether this requires a linear logic
		 */
		public boolean isLinear() {
			return this == Linear || this == Linear_with_guesses;
		}
		
		/**
		 * @return whether analysis is disabled
		 */
		public boolean isDisabled() {
			return this == Disabled;
		}
		
		/**
		 * @return whether eigenvalue guesses are required
		 */
		public boolean wantsGuesses() {
			return this == Linear_with_guesses;
		}
		
		/**
		 * @return a list of all possible choices
		 */
		public static AnalysisType[] allChoices() {
			return new AnalysisType[]
					{ Disabled, Linear, Linear_with_guesses, Nonlinear };
		}
	}
	
	/**
	 * Number of strict supporting invariants for each Motzkin transformation.
	 * Strict supporting invariants are invariants of the form
	 * <pre>Σ c_i x_i + c > 0.</pre>
	 * 
	 * The value must be non-negative; set to 0 to disable the use of strict
	 * supporting invariants.  Note that increasing this number will
	 * dramatically increase runtime!
	 * 
	 * @see num_non_strict_invariants
	 */
	public int num_strict_invariants = 1; // Default: 1
	
	/**
	 * Number of non-strict supporting invariants for each Motzkin
	 * transformation.  Strict supporting invariants are invariants of the form
	 * <pre>Σ c_i x_i + c ≥ 0.</pre>
	 * 
	 * The value must be non-negative; set to 0 to disable the use of strict
	 * supporting invariants.  Note that increasing this number will
	 * dramatically increase runtime!
	 * 
	 * @see num_strict_invariants
	 */
	public int num_non_strict_invariants = 0; // Default: 0
	
	/**
	 * Consider only non-decreasing invariants?
	 */
	public boolean nondecreasing_invariants = false; // Default: false
	
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
	 * Should we try to simplify the discovered ranking function and
	 * supporting invariants?
	 * 
	 * Note: this is quite expensive, it requires many calls to the solver:
	 * O((number of variables)*(number of supporting invariants))
	 * If the solver efficiently supports push() and pop(),
	 * this might be reasonably fast.
	 */
	public boolean simplify_result = false; // Default: false
	
	/**
	 * What analysis type should be used for the termination analysis?
	 * Use a linear SMT query, use a linear SMT query but guess some eigenvalues
	 * of the loop, or use a nonlinear SMT query?
	 */
	public AnalysisType termination_analysis = AnalysisType.Linear_with_guesses;
		// Default: AnalysisType.LINEAR_PLUS_GUESSES
	
	/**
	 * What analysis type should be used for the nontermination analysis?
	 * Use a linear SMT query, use a linear SMT query but guess some eigenvalues
	 * of the loop, or use a nonlinear SMT query?
	 */
	public AnalysisType nontermination_analysis = AnalysisType.Linear_with_guesses;
		// Default: AnalysisType.LINEAR_PLUS_GUESSES
	
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
	 * Build a string descriptions of the current preferences
	 */
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Number of strict supporting invariants: ");
		sb.append(this.num_strict_invariants);
		sb.append("\nNumber of non-strict supporting invariants: ");
		sb.append(this.num_non_strict_invariants);
		sb.append("\nConsider only non-deceasing supporting invariants: ");
		sb.append(this.nondecreasing_invariants);
		sb.append("\nCompute integeral hull: ");
		sb.append(this.compute_integral_hull);
		sb.append("\nTerm annotations enabled: ");
		sb.append(this.annotate_terms);
		sb.append("\nResult simplification enabled: ");
		sb.append(this.simplify_result);
		sb.append("\nTermination analysis: ");
		sb.append(this.termination_analysis);
		sb.append("\nNontermination analysis: ");
		sb.append(this.nontermination_analysis);
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