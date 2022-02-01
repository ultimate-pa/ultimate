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
package de.uni_freiburg.informatik.ultimate.lassoranker;

/**
 * Enum for different types of termination and nontermination analysis
 *
 * @author Jan Leike
 */
public enum AnalysisType {
	/**
	 * Do not do any analysis (this is the fastest ^^).
	 */
	DISABLED,

	/**
	 * Use only linear SMT solving. Fast but incomplete.
	 */
	LINEAR,

	/**
	 * Use linear SMT solving, but use a number of guesses for eigenvalues of the loop to retain more solution compared
	 * to plain linear SMT solving.
	 */
	LINEAR_WITH_GUESSES,

	/**
	 * Use nonlinear constraint solving. This is relatively complete but generally the slowest.
	 */
	NONLINEAR;

	/**
	 * @return whether this requires a linear logic
	 */
	public boolean isLinear() {
		return this == LINEAR || this == LINEAR_WITH_GUESSES;
	}

	/**
	 * @return whether analysis is disabled
	 */
	public boolean isDisabled() {
		return this == DISABLED;
	}

	/**
	 * @return whether eigenvalue guesses are required
	 */
	public boolean wantsGuesses() {
		return this == LINEAR_WITH_GUESSES;
	}

}
