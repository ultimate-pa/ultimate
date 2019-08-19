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
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Data structure for a (possibly) array select expression.
 * In the array theory of SMT-LIB the Array sort has only two parameters one
 * for the index and one for the value.
 * We model multidimensional arrays by nesting arrays. E.g. an array with two
 * integer indices and real values has the following Sort.
 * (Array Int -> (Array Int -> Real))
 * The select function has the following signature. (select (Array X Y) X Y)
 * Hence we have to use nested select expressions for multidimensional array
 * reads, e.g., in order to access the position (i1,i2) of an array we use the
 * following term. ("select" ("select" a i1) i2)
 * This is data structure is a wrapper for such a nested select expression which
 * allows you to directly access the array and the indices.
 * This data structure allows also multidimensional arrays of dimension 0. In
 * this case, mArray is null, mIndex is empty and mSelectTerm is some term.
 * @author Matthias Heizmann
 *
 */
public class MultiDimensionalSelect {

	private final Term mArray;
	private final ArrayIndex mIndex;
	private final ApplicationTerm mSelectTerm;

	/**
	 * Translate a (possibly) nested SMT term into this data structure.
	 * @param term term of the form ("select" a i2) for some array a and some
	 * index i2.
	 */
	public MultiDimensionalSelect(Term term) {
		if (term instanceof ApplicationTerm) {
			mSelectTerm = (ApplicationTerm) term;
		} else {
			mSelectTerm = null;
		}
		final ArrayList<Term> index = new ArrayList<Term>();
		while (true) {
			if (!(term instanceof ApplicationTerm)) {
				break;
			}
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (!appTerm.getFunction().getName().equals("select")) {
				break;
			}
			assert appTerm.getParameters().length == 2;
			index.add(0,appTerm.getParameters()[1]);
			term = appTerm.getParameters()[0];
		}
		mIndex = new ArrayIndex(index);
		mArray = term;
		assert classInvariant();
	}



	public MultiDimensionalSelect(final Term array, final ArrayIndex index, final Script script) {
		super();
		mArray = array;
		mIndex = index;
		Term tmp = array;
		for (final Term entry : index) {
			tmp = SmtUtils.select(script, tmp, entry);
		}
		mSelectTerm = (ApplicationTerm) tmp;
	}

	/**
	 * Extract from this {@link MultiDimensionalSelect} the
	 * {@link MultiDimensionalSelect} on the innermost dim dimensions. That is the
	 * {@link MultiDimensionalSelect}
	 * <ul>
	 * <li>whose array is the same as the array of this
	 * {@link MultiDimensionalSelect}
	 * <li>whose index consists only of the first dim entries of this arrays' index,
	 * and
	 * <li>whose SMT sort is dim dimensions higher than the sort of this
	 * {@link MultiDimensionalSelect}. E.g., if the sort of this
	 * {@link MultiDimensionalSelect} is Int (hence 0-dimensional) and dim=2 then
	 * the sort of the returned {@link MultiDimensionalSelect} is a 2-dimensional
	 * array.
	 * </ul>
	 */
	public MultiDimensionalSelect getInnermost(final int dim) {
		if (dim < 1) {
			throw new IllegalArgumentException("result must have at least dimension one");
		}
		if (dim > getDimension()) {
			throw new IllegalArgumentException("cannot extract more dimensions than this array has");
		}
		ArraySelect as = ArraySelect.convert(mSelectTerm);
		for (int i = 0; i < getDimension() - dim; i++) {
			as = ArraySelect.convert(as.getArray());
		}
		return MultiDimensionalSelect.convert(as.asTerm());
	}



	private boolean classInvariant() {
		if (mArray == null) {
			return mIndex.size() == 0;
		} else {
			return MultiDimensionalSort.
					areDimensionsConsistent(mArray, mIndex, mSelectTerm);
		}
	}

	public Term getArray() {
		return mArray;
	}

	public ArrayIndex getIndex() {
		return mIndex;
	}

	public ApplicationTerm getSelectTerm() {
		return mSelectTerm;
	}

	public int getDimension() {
		return getIndex().size();
	}

	public Term toTerm(final Script script) {
		return SmtUtils.multiDimensionalSelect(script, getArray(), getIndex());
	}


	public static MultiDimensionalSelect convert(final Term term) {
		if (!(term instanceof ApplicationTerm)) {
			return null;
		}
		final MultiDimensionalSelect mds = new MultiDimensionalSelect(term);
		if (mds.getArray() == null) {
			return null;
		} else {
			return mds;
		}
	}

	@Override
	public String toString() {
		return mSelectTerm.toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj instanceof MultiDimensionalSelect) {
			return mSelectTerm.equals(((MultiDimensionalSelect) obj).getSelectTerm());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return mSelectTerm.hashCode();
	}


	/**
	 * Return all MultiDimensionalSelect Objects for all multidimensional
	 * select expressions that occur in term.
	 * If one multidimensional expression occurs in another multidimensional
	 * select expression (e.g. as index) the nested one is not returned by
	 * this method.
	 * If an select term occurs multiple times it is contained multiple times
	 * in the result.
	 * @param allowArrayValues allow also MultiDimensionalSelect terms whose
	 * Sort is an array Sort (these select terms occur usually in
	 * multidimensional store terms).
	 */
	public static List<MultiDimensionalSelect> extractSelectShallow(
			final Term term, final boolean allowArrayValues) {
		final List<MultiDimensionalSelect> result = new ArrayList<MultiDimensionalSelect>();
		final Set<ApplicationTerm> selectTerms =
				(new ApplicationTermFinder("select", true)).findMatchingSubterms(term);
		for (final Term storeTerm : selectTerms) {
			if (allowArrayValues || !storeTerm.getSort().isArraySort()) {
				final MultiDimensionalSelect mdSelect = new MultiDimensionalSelect(storeTerm);
				if (mdSelect.getIndex().size() == 0) {
					throw new AssertionError("select must not have dimension 0");
				}
				result.add(mdSelect);
			}
		}
		return result;
	}

	/**
	 * Return all MultiDimensionalSelect Objects for all select expressions
	 * that occur in term. This method also return the inner multidimensional
	 * select expressions in other multidimensional select expressions.
	 * If an select term occurs multiple times it is contained multiple times
	 * in the result.
	 * If multidimensional selects are nested, the inner ones occur earlier
	 * in the resulting list.
	 * @param allowArrayValues allow also MultiDimensionalSelect terms whose
	 * Sort is an array Sort (these select terms occur usually in
	 * multidimensional store terms).
	 */
	public static List<MultiDimensionalSelect> extractSelectDeep(
			final Term term, final boolean allowArrayValues) {
		final List<MultiDimensionalSelect> result = new LinkedList<MultiDimensionalSelect>();
		List<MultiDimensionalSelect> foundInThisIteration = extractSelectShallow(term, allowArrayValues);
		while (!foundInThisIteration.isEmpty()) {
			result.addAll(0, foundInThisIteration);
			final List<MultiDimensionalSelect> foundInLastIteration = foundInThisIteration;
			foundInThisIteration = new ArrayList<MultiDimensionalSelect>();
			for (final MultiDimensionalSelect mdSelect : foundInLastIteration) {
				foundInThisIteration.addAll(extractSelectShallow(mdSelect.getArray(), allowArrayValues));
				final ArrayIndex index = mdSelect.getIndex();
				for (final Term entry : index) {
					foundInThisIteration.addAll(extractSelectShallow(entry, allowArrayValues));
				}
			}
		}
		return result;
	}
}
