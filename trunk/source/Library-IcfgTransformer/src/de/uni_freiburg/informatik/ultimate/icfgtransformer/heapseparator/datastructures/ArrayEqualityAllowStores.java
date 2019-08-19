/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayEquality.ArrayEqualityException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateException;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Union type for all ways of equating to Terms that have array type.
 *
 * Note: We assume that the only relation over array-type Terms is "=".
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ArrayEqualityAllowStores {

	ArrayUpdate mArrayUpdate;

	ArrayEquality mArrayEquality;

	boolean mOtherIsNegated;
	Pair<Term, Term> mOther;

	public ArrayEqualityAllowStores(final ArrayUpdate arrayUpdate) {
		mArrayUpdate = arrayUpdate;
		mArrayEquality = null;
		mOtherIsNegated = false;
		mOther = null;
	}

	public ArrayEqualityAllowStores(final ArrayEquality arrayEquality) {
		mArrayUpdate = null;
		mArrayEquality = arrayEquality;
		mOtherIsNegated = false;
		mOther = null;
	}

	public ArrayEqualityAllowStores(final Term lhs, final Term rhs, final boolean isNegated) {
		mArrayUpdate = null;
		mArrayEquality = null;
		mOtherIsNegated = isNegated;
		mOther = new Pair<>(lhs, rhs);
	}

	public Term getTerm(final Script script) {
		if (mArrayUpdate != null) {
			return mArrayUpdate.getArrayUpdateTerm();
		}
		if (mArrayEquality != null) {
			return mArrayEquality.getOriginalTerm();
		}
		assert mOther != null;
		Term result = SmtUtils.binaryEquality(script, mOther.getFirst(), mOther.getSecond());
		if (mOtherIsNegated) {
			result = SmtUtils.not(script, result);
		}
		return result;
	}

	public static List<ArrayEqualityAllowStores> extractArrayEqualityAllowStores(final Term formula) {
		final HashSet<String> functionSymbolNames = new HashSet<>(3);
		functionSymbolNames.add("=");
		functionSymbolNames.add("distinct");
		functionSymbolNames.add("not");

		final List<ArrayEqualityAllowStores> result = new ArrayList<>();

		final ApplicationTermFinder atf = new ApplicationTermFinder(functionSymbolNames, false);
		for (final ApplicationTerm subterm : atf.findMatchingSubterms(formula)) {
			ArrayEqualityAllowStores arrayRel = null;

			final boolean isNegated = subterm.getFunction().getName().equals("not")
					|| subterm.getFunction().getName().equals("distinct");

			final Term lhs;
			final Term rhs;
			if (subterm.getFunction().getName().equals("not")) {
				final Term notArg = subterm.getParameters()[0];
				if (!(notArg instanceof ApplicationTerm)) {
					continue;
				}

				final ApplicationTerm notArgAt = (ApplicationTerm) notArg;

				if (!notArgAt.getFunction().getName().equals("=")) {
					continue;
				}
				lhs = notArgAt.getParameters()[0];
				rhs = notArgAt.getParameters()[1];

				if (!lhs.getSort().isArraySort()) {
					continue;
				}
			} else {
				lhs = subterm.getParameters()[0];
				rhs = subterm.getParameters()[1];
				if (!lhs.getSort().isArraySort()) {
					continue;
				}
			}

			try {
				arrayRel = new ArrayEqualityAllowStores(new ArrayUpdate(subterm, isNegated, false));
				result.add(arrayRel);
				continue;
			} catch (final ArrayUpdateException e) {
				// do nothing/fall through
			}

			try {
				arrayRel = new ArrayEqualityAllowStores(new ArrayEquality(subterm, true, true));
				result.add(arrayRel);
				continue;
			} catch (final ArrayEqualityException e) {
				// do nothing/fall through
			}

			result.add(new ArrayEqualityAllowStores(lhs, rhs, isNegated));
		}
		return result;

	}

	/**
	 * get the simple array on the left hand side of the equation
	 *
	 * @return
	 */
	public Term getLhsArray() {
		if (mArrayUpdate != null) {
			return mArrayUpdate.getNewArray();
		}
		if (mArrayEquality != null) {
			return mArrayEquality.getLhs();
		}
		if (mOther != null) {
			throw new UnsupportedOperationException("implement this, when it occurs..");
		}
		throw new AssertionError();
	}

	/**
	 *
	 * get the simple array on the left hand side of the equation
	 *
	 * @return
	 */
	public Term getRhsArray() {
		if (mArrayUpdate != null) {
			return mArrayUpdate.getOldArray();
		}
		if (mArrayEquality != null) {
			return mArrayEquality.getRhs();
		}
		if (mOther != null) {
			throw new UnsupportedOperationException("implement this, when it occurs..");
		}
		throw new AssertionError();
	}
}
