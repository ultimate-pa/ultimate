/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface ITerminationAnalysisSettings {

	/**
	 * What analysis type should be used for the termination analysis? Use a linear SMT query, use a linear SMT query
	 * but guess some eigenvalues of the loop, or use a nonlinear SMT query?
	 */
	AnalysisType getAnalysis();

	/**
	 * Number of strict supporting invariants for each Motzkin transformation. Strict supporting invariants are
	 * invariants of the form
	 *
	 * <pre>
	 * Σ c_i x_i + c > 0.
	 * </pre>
	 *
	 * The value must be non-negative; set to 0 to disable the use of strict supporting invariants. Note that increasing
	 * this number will dramatically increase runtime!
	 *
	 * @see #getNumNonStrictInvariants()
	 */
	int getNumStrictInvariants();

	/**
	 * Number of non-strict supporting invariants for each Motzkin transformation. Strict supporting invariants are
	 * invariants of the form
	 *
	 * <pre>
	 * Σ c_i x_i + c ≥ 0.
	 * </pre>
	 *
	 * The value must be non-negative; set to 0 to disable the use of strict supporting invariants. Note that increasing
	 * this number will dramatically increase runtime!
	 *
	 * @see #getNumStrictInvariants()
	 */
	int getNumNonStrictInvariants();

	/**
	 * Consider only non-decreasing invariants?
	 */
	boolean isNonDecreasingInvariants();

	/**
	 * Should we try to simplify the discovered ranking function and supporting invariants?
	 *
	 * Note: this is quite expensive, it requires many calls to the solver: O((number of variables)*(number of
	 * supporting invariants)) If the solver efficiently supports push() and pop(), this might be reasonably fast.
	 */
	boolean isSimplifyTerminationArgument();

	/**
	 * Should we try to simplify the termination argument's supporting invariants?
	 */
	boolean isSimplifySupportingInvariants();

	/**
	 * Should we try to simplify the stem transition and reduce disjunctions? This generally incomplete but it increases
	 * performance a bunch if the stem has many disjuncts.
	 */
	boolean isOverapproximateStem();

}