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
	public int num_non_strict_invariants = 1; // Default: 1
	
	/**
	 * Only consider non-decreasing invariants.
	 */
	public boolean only_nondecreasing_invariants = false; // Default: false
	
	/**
	 * Should the polyhedra for stem and loop be made integral for integer
	 * programs?
	 */
	public boolean compute_integral_hull = false; // not yet implemented
	
	/**
	 * Are disjunctions allowed in the stem and loop transition?
	 */
	public boolean enable_disjunction = true; // Default: true
	
	/**
	 * Add annotations to terms for debugging purposes and/or to make use
	 * of unsatisfiable cores
	 */
	public boolean annotate_terms = true; // Default: true
	
	/**
	 * Use a nonlinear SMT query for checking nontermination?
	 */
	public boolean nontermination_check_nonlinear = true; // Default: true
	
	/**
	 * Use a nonlinear SMT query for checking termination?
	 */
	public boolean termination_check_nonlinear = true; // Default: true
	
	/**
	 * What shell command should be used to call the external smt solver?
	 */
	public String smt_solver_command = "z3 -smt2 -in SMTLIB2_COMPLIANT=true ";
	
	/**
	 * Write SMT solver script to file.
	 */
	public boolean dumpSmtSolverScript = false;
	
	/**
	 * File to which the SMT solver script is written.
	 */
	public String fileNameOfDumpedScript = "LassoRankerScript.smt2";
	
	/**
	 * Build a string descriptions of the current preferences
	 */
	public String show() {
		StringBuilder sb = new StringBuilder();
		sb.append("Number of strict supporting invariants: ");
		sb.append(this.num_strict_invariants);
		sb.append("\nNumber of non-strict supporting invariants: ");
		sb.append(this.num_non_strict_invariants);
		sb.append("\nConsider non-deceasing supporting invariants: ");
		sb.append(this.only_nondecreasing_invariants);
		sb.append("\nCompute integeral hull: ");
		sb.append(this.compute_integral_hull);
		sb.append("\nEnable disjunction: ");
		sb.append(this.enable_disjunction);
		sb.append("\nTerm annotations enabled: ");
		sb.append(this.annotate_terms);
		sb.append("\nNonlinear nontermination check: ");
		sb.append(this.nontermination_check_nonlinear);
		sb.append("\nNonlinear termination check: ");
		sb.append(this.termination_check_nonlinear);
		sb.append("\nSMT solver command: ");
		sb.append(this.smt_solver_command);
		sb.append("\nDump SMT script to file: ");
		sb.append(this.dumpSmtSolverScript);
		sb.append("\nFilename of dumped script: ");
		sb.append(this.fileNameOfDumpedScript);
		return sb.toString();
	}
}