/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Wrapper for an equality of the form a1=a2, where a1 and a2 are TermVariables.
 * In the future we may extend in a way that a1 and a2 can be constants (i.e.
 * 0-ary function symbols).
 * @author Matthias Heizmann
 */
public class ArrayEquality {
	private final Term mOriginalTerm;
	private final Term mLhs;
	private final Term mRhs;
	/*
	 * this represents a disequality instead of an equality
	 */
	private final boolean mIsNegated;

	public ArrayEquality(final Term term) throws ArrayEqualityException {
		this(term, false, false);
	}

	public ArrayEquality(final Term term, final boolean allowDisequalities, final boolean allowConstants)
					throws ArrayEqualityException {

		if (!(term instanceof ApplicationTerm)) {
			throw new ArrayEqualityException("no ApplicationTerm");
		}

		final ApplicationTerm appTerm = (ApplicationTerm) term;


		final boolean isNotEqualsAppTerm = (appTerm.getFunction().getName().equals("not")
				&& appTerm.getParameters()[0] instanceof ApplicationTerm
				&& ((ApplicationTerm) appTerm.getParameters()[0]).getFunction().getName().equals("="));
		final boolean isDisEquality = appTerm.getFunction().getName().equals("distinct")
				|| isNotEqualsAppTerm;

		mIsNegated = isDisEquality;

		if (!appTerm.getFunction().getName().equals("=")) {
			if (!allowDisequalities) {
				throw new ArrayEqualityException("no equality");
			} else if(!isDisEquality) {
				throw new ArrayEqualityException("no (dis)equality");
			}
		}

		final ApplicationTerm eqAppTerm = isNotEqualsAppTerm ?
				(ApplicationTerm) appTerm.getParameters()[0] :
					appTerm;

		if (eqAppTerm.getParameters().length != 2) {
			throw new ArrayEqualityException("no binary equality");
		}
		mOriginalTerm = term;
		final Term lhsTerm = eqAppTerm.getParameters()[0];
		final Term rhsTerm = eqAppTerm.getParameters()[1];
		if (!(lhsTerm.getSort().isArraySort())) {
			throw new ArrayEqualityException("no array");
		}

		if (lhsTerm instanceof TermVariable) {
			mLhs = lhsTerm;
		} else if (allowConstants && isTermVarOrConst(lhsTerm)) {
			mLhs = lhsTerm;
		} else {
			throw new ArrayEqualityException("no TermVariable or constant");
		}

		if (rhsTerm instanceof TermVariable) {
			mRhs = rhsTerm;
		} else if (allowConstants && isTermVarOrConst(rhsTerm)) {
			mRhs = rhsTerm;
		} else {
			throw new ArrayEqualityException("no TermVariable or constant");
		}
	}

	public Term getOriginalTerm() {
		return mOriginalTerm;
	}

	public Term getLhs() {
		return mLhs;
	}

	public Term getRhs() {
		return mRhs;
	}

	public TermVariable getLhsTermVariable() {
		return (TermVariable) mLhs;
	}

	public TermVariable getRhsTermVariable() {
		return (TermVariable) mRhs;
	}

	public boolean isNegated() {
		return mIsNegated;
	}

	public static List<ArrayEquality> extractArrayEqualities(final Term term) {
		final HashSet<String> functionSymbolNames = new HashSet<>(3);
		functionSymbolNames.add("=");
		functionSymbolNames.add("distinct");
		functionSymbolNames.add("not");

		final List<ArrayEquality> result = new ArrayList<>();

		final ApplicationTermFinder atf = new ApplicationTermFinder(functionSymbolNames, false);
		for (final ApplicationTerm subterm : atf.findMatchingSubterms(term)) {
			ArrayEquality arrayEquality = null;
			try {
				arrayEquality = new ArrayEquality(subterm, true, true);
			} catch (final ArrayEqualityException e) {
				continue;
			}
			result.add(arrayEquality);
		}
		return result;
	}

	private static boolean isTermVarOrConst(final Term t) {
		if (t instanceof TermVariable) {
			return true;
		} else if (t instanceof ConstantTerm) {
			return true;
		} else if (t instanceof ApplicationTerm
				&& ((ApplicationTerm) t).getParameters().length == 0) {
			return true;
		}
		return false;
	}

	@Override
	public String toString() {
		return mOriginalTerm.toString();
	}

	public class ArrayEqualityException extends Exception {

		private static final long serialVersionUID = -5344050289008681972L;

		public ArrayEqualityException(final String message) {
			super(message);
		}
	}

	/**
	 * Given an array of terms, partition them into terms that are array
	 * equalities and terms that are not array equalities.
	 */
	public static class ArrayEqualityExtractor {
		private final List<ArrayEquality> mArrayEqualities = new ArrayList<ArrayEquality>();
		private final List<Term> remainingTerms = new ArrayList<Term>();

		public ArrayEqualityExtractor(final Term[] terms) {
			for (final Term term : terms) {
				ArrayEquality au;
				try {
					au = new ArrayEquality(term);
				} catch (final ArrayEqualityException e) {
					au = null;
				}
				if (au == null) {
					remainingTerms.add(term);
				} else {
					mArrayEqualities.add(au);
				}
			}
		}

		public List<ArrayEquality> getArrayEqualities() {
			return mArrayEqualities;
		}

		public List<Term> getRemainingTerms() {
			return remainingTerms;
		}
	}

}
