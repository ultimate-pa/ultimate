/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;


/**
 * Various (local) settings for termination analysis
 * 
 * A new TerminationAnalysisSettings object can be used for each template
 * 
 * This class functions much like a struct and is implemented like one.
 * 
 * @author Jan Leike
 */
public class TerminationAnalysisSettings implements Serializable {
	private static final long serialVersionUID = 9183092457990345360L;
	
	/**
	 * What analysis type should be used for the termination analysis?
	 * Use a linear SMT query, use a linear SMT query but guess some eigenvalues
	 * of the loop, or use a nonlinear SMT query?
	 */
	public AnalysisType analysis = AnalysisType.LINEAR;
		// Default: AnalysisType.LINEAR_PLUS_GUESSES
	
	/**
	 * Number of strict supporting invariants for each Motzkin transformation.
	 * Strict supporting invariants are invariants of the form
	 * <pre>Σ c_i x_i + c > 0.</pre>
	 * 
	 * The value must be non-negative; set to 0 to disable the use of strict
	 * supporting invariants.  Note that increasing this number will
	 * dramatically increase runtime!
	 * 
	 * @see numnon_strict_invariants
	 */
	public int numstrict_invariants = 1; // Default: 1
	
	/**
	 * Number of non-strict supporting invariants for each Motzkin
	 * transformation.  Strict supporting invariants are invariants of the form
	 * <pre>Σ c_i x_i + c ≥ 0.</pre>
	 * 
	 * The value must be non-negative; set to 0 to disable the use of strict
	 * supporting invariants.  Note that increasing this number will
	 * dramatically increase runtime!
	 * 
	 * @see numstrict_invariants
	 */
	public int numnon_strict_invariants = 0; // Default: 0
	
	/**
	 * Consider only non-decreasing invariants?
	 */
	public boolean nondecreasing_invariants = false; // Default: false
	
	/**
	 * Should we try to simplify the discovered ranking function and
	 * supporting invariants?
	 * 
	 * Note: this is quite expensive, it requires many calls to the solver:
	 * O((number of variables)*(number of supporting invariants))
	 * If the solver efficiently supports push() and pop(),
	 * this might be reasonably fast.
	 */
	public boolean simplify_termination_argument = true; // Default: true
	
	/**
	 * Should we try to simplify the termination argument's
	 * supporting invariants?
	 */
	public boolean simplify_supporting_invariants = true; // Default: true
	
	/**
	 * Should we try to simplify the stem transition and reduce disjunctions?
	 * This generally incomplete but it increases performance a bunch if
	 * the stem has many disjuncts.
	 */
	public boolean overapproximate_stem = false; // Default: false
	
	/**
	 * Default construction initializes default values
	 */
	public TerminationAnalysisSettings() {
	}
	
	/**
	 * Copy constructor copies everything
	 */
	public TerminationAnalysisSettings(TerminationAnalysisSettings other) {
		analysis = other.analysis;
		numstrict_invariants = other.numstrict_invariants;
		numnon_strict_invariants = other.numnon_strict_invariants;
		nondecreasing_invariants = other.nondecreasing_invariants;
		simplify_termination_argument =
				other.simplify_termination_argument;
	}
	
	/**
	 * Verify that the settings are self-consistent and sane.
	 * Only makes assertion calls.
	 */
	public void checkSanity() {
		assert numstrict_invariants >= 0;
		assert numnon_strict_invariants >= 0;
	}
	
	/**
	 * Build a string description of the current preferences
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Termination analysis: ");
		sb.append(analysis);
		sb.append("\nNumber of strict supporting invariants: ");
		sb.append(numstrict_invariants);
		sb.append("\nNumber of non-strict supporting invariants: ");
		sb.append(numnon_strict_invariants);
		sb.append("\nConsider only non-deceasing supporting invariants: ");
		sb.append(nondecreasing_invariants);
		sb.append("\nSimplify termination arguments: ");
		sb.append(simplify_termination_argument);
		sb.append("\nSimplify supporting invariants: ");
		sb.append(simplify_supporting_invariants);
		sb.append("Overapproximate stem: ");
		sb.append(overapproximate_stem);
		return sb.toString();
	}
}
