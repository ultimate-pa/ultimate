/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;

/**
 * Result of a pairwise equality analysis for a set of Terms.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class EqualityAnalysisResult {

	private final Set<Doubleton<Term>> mEqualDoubletons;
	private final Set<Doubleton<Term>> mDistinctDoubletons;
	private final Set<Doubleton<Term>> mUnknownDoubletons;

	public EqualityAnalysisResult(final Set<Doubleton<Term>> equalDoubletons,
			final Set<Doubleton<Term>> distinctDoubletons, final Set<Doubleton<Term>> unknownDoubletons) {
		super();
		mEqualDoubletons = equalDoubletons;
		mDistinctDoubletons = distinctDoubletons;
		mUnknownDoubletons = unknownDoubletons;
	}

	public EqualityAnalysisResult(final Set<Doubleton<Term>> doubletons) {
		super();
		final Set<Doubleton<Term>> emptySet = Collections.emptySet();
		mEqualDoubletons = emptySet;
		mDistinctDoubletons = emptySet;
		mUnknownDoubletons = doubletons;
	}

	/**
	 * @return all Doubletons (t1,t2) such that our analysis was able to prove that t1==t2 holds.
	 */
	public Set<Doubleton<Term>> getEqualDoubletons() {
		return mEqualDoubletons;
	}

	/**
	 * @return all Doubletons (t1,t2) such that our analysis was able to prove that t1!=t2 holds.
	 */
	public Set<Doubleton<Term>> getDistinctDoubletons() {
		return mDistinctDoubletons;
	}

	/**
	 * @return all Doubletons (t1,t2) such that our analysis was neither able to prove that t1==t2 holds nor that t1!=t2
	 *         holds.
	 */
	public Set<Doubleton<Term>> getUnknownDoubletons() {
		return mUnknownDoubletons;
	}

	/**
	 * @return a possibly simplified version of the term (= t1 t2) for a given Doubleton (t1,t2).
	 */
	public static Term equalTerm(final Script script, final Doubleton<Term> doubleton) {
		return SmtUtils.binaryEquality(script, doubleton.getOneElement(), doubleton.getOtherElement());
	}

	/**
	 * @return a possibly simplified version of the term (not (= t1 t2)) for a given Doubleton (t1,t2).
	 */
	public static Term notEqualTerm(final Script script, final Doubleton<Term> doubleton) {
		return SmtUtils.not(script, equalTerm(script, doubleton));
	}

	/**
	 * @return a list of all inferred equalities where each equality is given as an SMT term.
	 */
	public List<Term> constructListOfEqualities(final Script script) {
		final List<Term> result = new ArrayList<>();
		for (final Doubleton<Term> doubleton : getEqualDoubletons()) {
			result.add(equalTerm(script, doubleton));
		}
		return result;
	}

	/**
	 * @return a list of all inferred not-equals relations where each not-equals relation is given as an SMT term.
	 */
	public List<Term> constructListOfNotEquals(final Script script) {
		final List<Term> result = new ArrayList<>();
		for (final Doubleton<Term> doubleton : getDistinctDoubletons()) {
			result.add(notEqualTerm(script, doubleton));
		}
		return result;
	}

	/**
	 * @return Equality status of a Doubleton that was analyzed.
	 * @throws IllegalArgumentException
	 *             for Doubletons that were not analyzed
	 */
	public EqualityStatus getEqualityStatus(final Doubleton<Term> doubleton) {
		if (mEqualDoubletons.contains(doubleton)) {
			return EqualityStatus.EQUAL;
		} else if (mDistinctDoubletons.contains(doubleton)) {
			return EqualityStatus.NOT_EQUAL;
		} else if (mUnknownDoubletons.contains(doubleton)) {
			return EqualityStatus.UNKNOWN;
		} else {
			throw new IllegalArgumentException("unacquainted doublton " + doubleton);
		}
	}

}
