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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Union type of ArraySelect and ArraySelectOverStore.
 * (EDIT: .. no more.. now it's a very simple wrapper for MultiDimensionalSelect..)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ArrayCellAccess {

	private final MultiDimensionalSelect mMdSelect;

	/**
	 * The "base" array, i.e. if we have a store as array term of mMdSelect, then this is the array that is stored to.
	 *  (otherwise it's just that array term of mMdSelect)
	 */
	private final Term mSimpleArrayTerm;

	public ArrayCellAccess(final MultiDimensionalSelect mdSelect) {
		mMdSelect = mdSelect;

		Term innerArrayTerm = mdSelect.getArray();
		while (SmtUtils.isFunctionApplication(innerArrayTerm, "store")) {
			innerArrayTerm = ((ApplicationTerm) innerArrayTerm).getParameters()[0];
		}
		mSimpleArrayTerm = innerArrayTerm;

	}

	public static List<ArrayCellAccess> extractArrayCellAccesses(final Term formula) {
		final List<ArrayCellAccess> result = new ArrayList<>();

		final List<MultiDimensionalSelect> mdSelects = MultiDimensionalSelect.extractSelectShallow(formula, true);

		mdSelects.forEach(mds -> result.add(new ArrayCellAccess(mds)));

		return result;
	}

	/**
	 * get the array of the underlying mdSelect (can be a store term)
	 * @return
	 */
	public Term getArray() {
		return mMdSelect.getArray();
	}

	/**
	 * get the array variable/constant (look inside store terms)
	 * @return
	 */
	public Term getSimpleArray() {
		return mSimpleArrayTerm;
	}

	public ArrayIndex getIndex() {
		return mMdSelect.getIndex();
	}

	public Term getTerm() {
		return mMdSelect.getSelectTerm();
	}

	@Override
	public String toString() {
		return mMdSelect.toString();
	}

	public Set<Integer> getDimensionsOfIndexTerm(final Term indexSubterm) {
		final Set<Integer> result = new HashSet<>();
		for (int dim = 0; dim < mMdSelect.getIndex().size(); dim++) {
			if (indexSubterm.equals(mMdSelect.getIndex().get(dim))) {
				result.add(dim);
			}
		}
		return result;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mMdSelect == null) ? 0 : mMdSelect.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final ArrayCellAccess other = (ArrayCellAccess) obj;
		if (mMdSelect == null) {
			if (other.mMdSelect != null) {
				return false;
			}
		} else if (!mMdSelect.equals(other.mMdSelect)) {
			return false;
		}
		return true;
	}
}
