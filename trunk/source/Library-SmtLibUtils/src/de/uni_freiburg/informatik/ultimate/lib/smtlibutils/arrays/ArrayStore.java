/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.Collection;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermWrapper;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Wrapper for `store` terms from the SMT theory of arrays.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class ArrayStore implements ITermWrapper {
	private final Term mArray;
	private final Term mIndex;
	private final Term mValue;
	private final Term mTerm;

	public ArrayStore(final Term array, final Term index, final Term value, final Term term) {
		mArray = array;
		mIndex = index;
		mValue = value;
		mTerm = term;
	}

	public Term getArray() {
		return mArray;
	}

	public Term getIndex() {
		return mIndex;
	}

	public Term getValue() {
		return mValue;
	}

	@Override
	public Term getTerm() {
		return mTerm;
	}

	@Override
	public String toString() {
		return String.valueOf(mTerm);
	}

	@Override
	public int hashCode() {
		// ArrayStores are similar if they have the same term.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mTerm == null) ? 0 : mTerm.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		// ArrayStores are similar if they have the same term.
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final ArrayStore other = (ArrayStore) obj;
		if (mTerm == null) {
			if (other.mTerm != null)
				return false;
		} else if (!mTerm.equals(other.mTerm))
			return false;
		return true;
	}

	public static ArrayStore of(final Term term) {
		if (!(term instanceof ApplicationTerm)) {
			return null;
		}
		final ApplicationTerm appTerm = (ApplicationTerm) term;
		if (!appTerm.getFunction().isIntern()) {
			return null;
		}
		if (!appTerm.getFunction().getName().equals("store")) {
			return null;
		}
		assert (appTerm.getParameters().length == 3);
		return new ArrayStore(appTerm.getParameters()[0], appTerm.getParameters()[1], appTerm.getParameters()[2],
				appTerm);
	}

	/**
	 *
	 * @param onlyOutermost if set to true we do not descend to subterms of a term
	 *                      that has been found
	 */
	public static Collection<ArrayStore> extractStores(final Term term, final boolean onlyOutermost) {
		final Set<ApplicationTerm> storeTerms = SmtUtils.extractApplicationTerms("store", term, onlyOutermost);
		return storeTerms.stream().map(ArrayStore::of).collect(Collectors.toList());
	}
}
