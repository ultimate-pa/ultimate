/*
 * Copyright (C) 2014 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class ArraySortInterpretation implements SortInterpretation {
	private final Model mModel;
	private final SortInterpretation mIndexSort;
	private final SortInterpretation mValueSort;

	private final HashMap<Map<Term, Term>, Map<Term, Term>> mUnifier;
	private final HashMap<Term, HashMap<Term, Term>> mDiffMap;

	public ArraySortInterpretation(final Model model, final SortInterpretation index,
			final SortInterpretation value) {
		mModel = model;
		mIndexSort = index;
		mValueSort = value;
		mUnifier = new HashMap<>();
		final Map<Term, Term> empty = Collections.emptyMap();
		mUnifier.put(empty, empty);
		mDiffMap = new HashMap<>();
	}

	@Override
	public Term getModelValue(final int idx, final Sort arraySort) {
		final Sort valueSort = arraySort.getArguments()[1];
		return createArray(Collections.emptyMap(), mValueSort.getModelValue(idx, valueSort), arraySort);
	}

	private Term createArray(final Map<Term, Term> mapping, final Term defaultValue, final Sort arraySort) {
		final Theory theory = defaultValue.getTheory();
		final FunctionSymbol constFunc = theory.getFunctionWithResult(SMTLIBConstants.CONST, null, arraySort,
				defaultValue.getSort());
		Term result = theory.term(constFunc, defaultValue);
		final ArrayDeque<Term> keys = new ArrayDeque<>(mapping.keySet());
		// build the store term from back to front
		while (!keys.isEmpty()) {
			final Term index = keys.removeLast();
			result = theory.term("store", result, index, mapping.get(index));
		}
		return result;
	}

	public Term getSelect(final Term storeTerm, final Term selectIndex) {
		ApplicationTerm arrayTerm = (ApplicationTerm) storeTerm;
		while (arrayTerm.getFunction().getName() == "store") {
			if (arrayTerm.getParameters()[1] == selectIndex) {
				return arrayTerm.getParameters()[2];
			}
			arrayTerm = (ApplicationTerm) arrayTerm.getParameters()[0];
		}
		assert arrayTerm.getFunction().getName() == SMTLIBConstants.CONST;
		return arrayTerm.getParameters()[0];
	}

	public Term normalizeStoreTerm(final Term storeTerm) {
		final Map<Term, Term> map = new LinkedHashMap<>();
		ApplicationTerm arrayTerm = (ApplicationTerm) storeTerm;
		while (arrayTerm.getFunction().getName() == "store") {
			final Term index = arrayTerm.getParameters()[1];
			if (!map.containsKey(index)) {
				map.put(index, arrayTerm.getParameters()[2]);
			}
			arrayTerm = (ApplicationTerm) arrayTerm.getParameters()[0];
		}
		assert arrayTerm.getFunction().getName() == SMTLIBConstants.CONST;
		final Term defaultValue = arrayTerm.getParameters()[0];
		for (final Iterator<Entry<Term, Term>> entryIterator = map.entrySet().iterator(); entryIterator.hasNext();) {
			final Entry<Term, Term> entry = entryIterator.next();
			if (entry.getValue() == defaultValue) {
				entryIterator.remove();
			}
		}
		Map<Term, Term> unified = mUnifier.get(map);
		if (unified == null) {
			mUnifier.put(map, map);
			unified = map;
		}
		return createArray(unified, defaultValue, storeTerm.getSort());
	}

	@Override
	public Term extendFresh(final Sort arraySort) {
		assert arraySort.getSortSymbol().getName() == "Array";
		final Sort indexSort = arraySort.getArguments()[0];
		final Sort valueSort = arraySort.getArguments()[1];
		final Term freshIndex = mIndexSort.extendFresh(indexSort);
		final Term value = mModel.getSecondValue(valueSort);
		final Map<Term, Term> map = Collections.singletonMap(freshIndex, value);
		final Map<Term, Term> old = mUnifier.put(map, map);
		assert old == null;
		return createArray(map, mModel.getSomeValue(valueSort), arraySort);
	}

	@Override
	public Term toSMTLIB(final Theory t, final Sort sort) {
		throw new InternalError("toSMTLIB called");
	}

	public void addDiff(final Term fstArray, final Term sndArray, final Term index) {
		HashMap<Term,Term> subMap = mDiffMap.get(fstArray);
		if (subMap == null) {
			subMap = new HashMap<>();
			mDiffMap.put(fstArray, subMap);
		}
		final Term old = subMap.put(sndArray, index);
		assert old == null;
	}

	public Term computeDiff(final Term fstArray, final Term sndArray, final Sort indexSort) {
		// first check diff map
		final Map<Term, Term> subMap = mDiffMap.get(fstArray);
		if (subMap != null) {
			final Term result = subMap.get(sndArray);
			if (result != null) {
				return result;
			}
		}

		// return canonical value if arrays equal
		if (fstArray == sndArray) {
			return mModel.getSomeValue(indexSort);
		}

		// no diff matches; search first explicit difference

		// first build the map from the second array term.
		final Map<Term, Term> secondValues = new HashMap<>();
		ApplicationTerm arrayTerm = (ApplicationTerm) sndArray;
		while (arrayTerm.getFunction().getName() == "store") {
			final Term index = arrayTerm.getParameters()[1];
			secondValues.put(index, arrayTerm.getParameters()[2]);
			arrayTerm = (ApplicationTerm) arrayTerm.getParameters()[0];
		}
		assert arrayTerm.getFunction().getName() == SMTLIBConstants.CONST;
		final Term secondDefault = arrayTerm.getParameters()[0];

		// check each entry in the first array term, whether it differs.
		arrayTerm = (ApplicationTerm) fstArray;
		while (arrayTerm.getFunction().getName() == "store") {
			final Term index = arrayTerm.getParameters()[1];
			Term secondValue = secondValues.get(index);
			if (secondValue == null) {
				secondValue = secondDefault;
			}
			// check if firstValue is defined there and differs.
			if (secondValue != arrayTerm.getParameters()[2]) {
				return index;
			}
			arrayTerm = (ApplicationTerm) arrayTerm.getParameters()[0];
		}
		assert arrayTerm.getFunction().getName() == SMTLIBConstants.CONST;
		// they must differ on default value, so just return a fresh value.
		assert secondDefault != arrayTerm.getParameters()[0];
		final Term diffIndex = mIndexSort.extendFresh(indexSort);
		// store the index for future use, so we will return it again.
		addDiff(fstArray, sndArray, diffIndex);
		return diffIndex;
	}

	public SortInterpretation getIndexInterpretation() {
		return mIndexSort;
	}

	public SortInterpretation getValueInterpretation() {
		return mValueSort;
	}

	@Override
	public void register(final Term t) {
	}
}
