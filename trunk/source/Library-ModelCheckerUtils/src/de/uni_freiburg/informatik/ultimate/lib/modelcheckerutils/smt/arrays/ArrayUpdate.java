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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.NoRelationOfThisKindException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Wrapper for an equality (resp. not equals relation) of the form
 * arr' = (store, arr, index, value),
 * where
 * the array arr' is a TermVariable, and
 * (store, arr, index, value) is a multidimensional store.
 * A boolean flag allows to put the requirenment that also arr is a
 * TermVariable.
 * @author Matthias Heizmann
 */
public class ArrayUpdate {
	private final TermVariable mNewArray;
	private final MultiDimensionalStore mMultiDimensionalStore;
	private final Term mArrayUpdateTerm;
	private final boolean mIsNegatedEquality;

	/**
	 * Construct ArrayUpdate wrapper from term. Throw an ArrayUpdateException if
	 * term is no array update.
	 */
	public ArrayUpdate(final Term term, final boolean isNegated,
			final boolean enforceThatOldArrayIsTermVariable) throws ArrayUpdateException {
		BinaryEqualityRelation ber = null;
		try {
			ber = new BinaryEqualityRelation(term);
		} catch (final NoRelationOfThisKindException e) {
			throw new ArrayUpdateException(e.getMessage());
		}
		if (isNegated && ber.getRelationSymbol() != RelationSymbol.DISTINCT) {
			throw new ArrayUpdateException("no negated array update");
		}
		if (!isNegated && ber.getRelationSymbol() != RelationSymbol.EQ) {
			throw new ArrayUpdateException("no not negated array update");
		}
		mArrayUpdateTerm = term;
		mIsNegatedEquality = isNegated;
		final Term lhs = ber.getLhs();
		final Term rhs = ber.getRhs();
		ApplicationTerm allegedStoreTerm;
		if (isArrayTermVariable(lhs)) {
			if (isStoreTerm(rhs)) {
				mNewArray = (TermVariable) lhs;
				allegedStoreTerm = (ApplicationTerm) rhs;
			} else {
				throw new ArrayUpdateException("no array update");
			}
		} else if (isArrayTermVariable(rhs)) {
			if (isStoreTerm(lhs)) {
				mNewArray = (TermVariable) rhs;
				allegedStoreTerm = (ApplicationTerm) lhs;
			} else {
				throw new ArrayUpdateException("no array update");
			}
		} else {
			throw new ArrayUpdateException("no array update");
		}
		assert allegedStoreTerm.getFunction().getName().equals("store");
		assert allegedStoreTerm.getParameters().length == 3;
		assert mNewArray.getSort() == allegedStoreTerm.getSort();

		mMultiDimensionalStore = MultiDimensionalStore.convert(allegedStoreTerm);
		if (mMultiDimensionalStore.getIndex().size() == 0) {
			throw new ArrayUpdateException("no multidimensional array");
		}
		if (!mMultiDimensionalStore.getArray().getSort().equals(mNewArray.getSort())) {
			throw new AssertionError("sort mismatch");
		}
		if (enforceThatOldArrayIsTermVariable &&
				!(mMultiDimensionalStore.getArray() instanceof TermVariable)) {
			throw new ArrayUpdateException("old array is no term variable");

		}
	}

	/**
	 * Returns true iff term is TermVariable and has array sort
	 */
	private boolean isArrayTermVariable(final Term term) {
		if (term instanceof TermVariable) {
			if (term.getSort().isArraySort()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Returns true iff term is ApplicationTerm whose function symbol is
	 * "store".
	 */
	private boolean isStoreTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("store")) {
				return true;
			}
		}
		return false;
	}

	/**
	 * If term is a term variable of Sort sort, return term as TermVariable,
	 * return null otherwise.
	 */
	TermVariable isArrayWithSort(final Term term, final Sort sort) {
		if (term instanceof TermVariable) {
			if (term.getSort().equals(sort)) {
				return (TermVariable) term;
			} else {
				return null;
			}
		} else {
			return null;
		}
	}

	public Term getOldArray() {
		return mMultiDimensionalStore.getArray();
	}
	public TermVariable getNewArray() {
		return mNewArray;
	}
	public ArrayIndex getIndex() {
		return mMultiDimensionalStore.getIndex();
	}
	public Term getValue() {
		return mMultiDimensionalStore.getValue();
	}
	public Term getArrayUpdateTerm() {
		return mArrayUpdateTerm;
	}
	public MultiDimensionalStore getMultiDimensionalStore() {
		return mMultiDimensionalStore;
	}

	public boolean isNegatedEquality() {
		return mIsNegatedEquality;
	}

	@Override
	public String toString() {
		return mArrayUpdateTerm.toString();
	}


	public static class ArrayUpdateException extends Exception {

		private static final long serialVersionUID = -5344050289008681972L;

		public ArrayUpdateException(final String message) {
			super(message);
		}
	}

	/**
	 * Given an array of terms, partition them into terms that are array updates
	 * and terms that are not array updates.
	 */
	public static class ArrayUpdateExtractor {
		private final Map<Term, Term> mStore2TermVariable =
				new HashMap<Term, Term>();
		private final List<ArrayUpdate> mArrayUpdates =
				new ArrayList<ArrayUpdate>();
		private final List<Term> remainingTerms =
				new ArrayList<Term>();

		/**
		 * If negatedUpdate is true we search for terms of the form
		 * (not (= a (store a' b c)))
		 */
		public ArrayUpdateExtractor(final boolean negatedUpdate,
				final boolean oldArrayIsTermVariable, final Term... terms) {
			for (final Term term : terms) {
				ArrayUpdate au;
				try {
					au = new ArrayUpdate(term, negatedUpdate, oldArrayIsTermVariable);
				} catch (final ArrayUpdateException e) {
					au = null;
				}
				if (au == null) {
					remainingTerms.add(term);
				} else {
					mArrayUpdates.add(au);
					mStore2TermVariable.put(
							au.getMultiDimensionalStore().getStoreTerm(),
							au.getNewArray());
				}
			}
		}

		public Map<Term, Term> getStore2TermVariable() {
			return mStore2TermVariable;
		}

		public List<ArrayUpdate> getArrayUpdates() {
			return mArrayUpdates;
		}

		public List<Term> getRemainingTerms() {
			return remainingTerms;
		}
	}


	/**
	 * Extract and wrap subterms that are array updates. Enforce that the right hand side is a TermVariable.
	 * @param formula
	 * @return
	 */
	public static List<ArrayUpdate> extractArrayUpdates(final Term formula) {
		return extractArrayUpdates(formula, true);
	}

	public static List<ArrayUpdate> extractArrayUpdates(final Term formula, final boolean enforceThatOldArrayIsTermVariable) {
		final HashSet<String> functionSymbolNames = new HashSet<>(3);
		functionSymbolNames.add("=");
		functionSymbolNames.add("distinct");
		functionSymbolNames.add("not");

		final List<ArrayUpdate> result = new ArrayList<>();

		final ApplicationTermFinder atf = new ApplicationTermFinder(functionSymbolNames, false);
		for (final ApplicationTerm subterm : atf.findMatchingSubterms(formula)) {
			ArrayUpdate arrayUpdate = null;

			final boolean isNegated = subterm.getFunction().getName().equals("not")
					|| subterm.getFunction().getName().equals("distinct");
			try {
				arrayUpdate = new ArrayUpdate(subterm, isNegated, enforceThatOldArrayIsTermVariable);
			} catch (final ArrayUpdateException e) {
				continue;
			}
			result.add(arrayUpdate);
		}
		return result;
	}
}
