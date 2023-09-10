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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
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
 * <br>
 * Note that due to the select-over-store optimization the resulting term may
 * not necessarily be an ApplicationTerm.
 * Note that we also allow indices of size 0 and hence every Term can be the
 * mArray or mSelectTerm of this class.
 * @author Matthias Heizmann
 *
 */
public class MultiDimensionalSelect implements ITermProvider {

	private final Term mArray;
	private final ArrayIndex mIndex;

	public MultiDimensionalSelect(final Term array, final ArrayIndex index) {
		super();
		mArray = array;
		mIndex = index;
	}

	/**
	 * Translate a (possibly) nested SMT term into this data structure.
	 * @param term term of the form ("select" a i2) for some array a and some
	 * index i2.
	 */
	public static MultiDimensionalSelect of(Term term) {
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
		if (index.isEmpty()) {
			return null;
		}
		return new MultiDimensionalSelect(term, new ArrayIndex(index));
	}

	public Term getArray() {
		return mArray;
	}

	public ArrayIndex getIndex() {
		return mIndex;
	}

	public int getDimension() {
		return getIndex().size();
	}

	/**
	 * Returns the sort of the select that is represented by this class.
	 */
	public Sort getSort() {
		Sort result = mArray.getSort();
		for (int i = 0; i < getDimension(); i++) {
			assert result.getArguments().length == 2;
			result = result.getArguments()[1];
		}
		return result;
	}

	@Override
	public Term toTerm(final Script script) {
		final Term result = SmtUtils.multiDimensionalSelect(script, getArray(), getIndex());
		assert result.getSort() == getSort();
		return result;
	}

	@Override
	public String toString() {
		// not SMT-LIB syntax, but easier to read
		return String.format("(select %s %s)", mArray, mIndex);
	}

	@Override
	public int hashCode() {
		return Objects.hash(mArray, mIndex);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final MultiDimensionalSelect other = (MultiDimensionalSelect) obj;
		return Objects.equals(mArray, other.mArray) && Objects.equals(mIndex, other.mIndex);
	}

	/**
	 * Return all MultiDimensionalSelect Objects for all multidimensional select
	 * expressions that occur in term. If one multidimensional expression occurs in
	 * another multidimensional select expression (e.g. as index) the nested one is
	 * not returned by this method. If an select term occurs multiple times it is
	 * contained multiple times in the result.
	 */
	public static List<MultiDimensionalSelect> extractSelectShallow(final Term term) {
		final List<MultiDimensionalSelect> result = new ArrayList<MultiDimensionalSelect>();
		final Set<ApplicationTerm> selectTerms = SmtUtils.extractApplicationTerms("select", term, true);
		for (final Term storeTerm : selectTerms) {
			final MultiDimensionalSelect mdSelect = MultiDimensionalSelect.of(storeTerm);
			if (mdSelect.getIndex().size() == 0) {
				throw new AssertionError("MultiDimensionalSelect must not have dimension 0 here");
			}
			result.add(mdSelect);
		}
		return result;
	}

	/**
	 * Return all MultiDimensionalSelect Objects for all select expressions that
	 * occur in term. This method also return the inner multidimensional select
	 * expressions in other multidimensional select expressions. If an select term
	 * occurs multiple times it is contained multiple times in the result. If
	 * multidimensional selects are nested, the inner ones occur earlier in the
	 * resulting list.
	 */
	public static List<MultiDimensionalSelect> extractSelectDeep(final Term term) {
		final List<MultiDimensionalSelect> result = new LinkedList<MultiDimensionalSelect>();
		List<MultiDimensionalSelect> foundInThisIteration = extractSelectShallow(term);
		while (!foundInThisIteration.isEmpty()) {
			result.addAll(0, foundInThisIteration);
			final List<MultiDimensionalSelect> foundInLastIteration = foundInThisIteration;
			foundInThisIteration = new ArrayList<MultiDimensionalSelect>();
			for (final MultiDimensionalSelect mdSelect : foundInLastIteration) {
				foundInThisIteration.addAll(extractSelectShallow(mdSelect.getArray()));
				final ArrayIndex index = mdSelect.getIndex();
				for (final Term entry : index) {
					foundInThisIteration.addAll(extractSelectShallow(entry));
				}
			}
		}
		return result;
	}
}
