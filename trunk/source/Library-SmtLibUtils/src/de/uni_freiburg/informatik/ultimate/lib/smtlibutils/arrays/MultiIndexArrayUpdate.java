/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MultiIndexArrayUpdate implements ITermProvider {
	private final RelationSymbol mRelationSymbol;
	private final Term mNewArray;
	private final MultiDimensionalNestedStore mMultiDimensionalNestedStore;

	public MultiIndexArrayUpdate(final RelationSymbol relationSymbol, final Term newArray,
			final MultiDimensionalNestedStore mdns) {
		mRelationSymbol = relationSymbol;
		mNewArray = newArray;
		mMultiDimensionalNestedStore = mdns;
	}

	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	public Term getNewArray() {
		return mNewArray;
	}

	public MultiDimensionalNestedStore getMultiDimensionalNestedStore() {
		return mMultiDimensionalNestedStore;
	}

	public MultiIndexArrayUpdate removeOneIndex(final int i) {
		return new MultiIndexArrayUpdate(getRelationSymbol(), getNewArray(),
				getMultiDimensionalNestedStore().removeOneIndex(i));
	}

	public boolean isNondeterministicUpdate() {
		for (int i = 0; i < mMultiDimensionalNestedStore.getIndices().size(); i++) {
			if (isNondeterministicUpdate(i)) {
				continue;
			} else {
				return false;
			}
		}
		return true;
	}

	/**
	 * The theory of arrays allows us to encode a nondeterministic update at index k
	 * as follows `a'= (store a k (select a' k))`. Note that this is only a
	 * nondeterministic update if there are no other constraints for a' at position
	 * k. This method detects nondeterministc updates that have exactly that form.
	 */
	public boolean isNondeterministicUpdate(final int i) {
		final ArrayIndex index = mMultiDimensionalNestedStore.getIndices().get(i);
		final Term value = mMultiDimensionalNestedStore.getValues().get(i);
		final MultiDimensionalSelect mds = MultiDimensionalSelect.of(value);
		return mds != null && mds.getArray() == getNewArray() && mds.getIndex().equals(index);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((mMultiDimensionalNestedStore == null) ? 0 : mMultiDimensionalNestedStore.hashCode());
		result = prime * result + ((mNewArray == null) ? 0 : mNewArray.hashCode());
		result = prime * result + ((mRelationSymbol == null) ? 0 : mRelationSymbol.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final MultiIndexArrayUpdate other = (MultiIndexArrayUpdate) obj;
		if (mMultiDimensionalNestedStore == null) {
			if (other.mMultiDimensionalNestedStore != null)
				return false;
		} else if (!mMultiDimensionalNestedStore.equals(other.mMultiDimensionalNestedStore))
			return false;
		if (mNewArray == null) {
			if (other.mNewArray != null)
				return false;
		} else if (!mNewArray.equals(other.mNewArray))
			return false;
		if (mRelationSymbol != other.mRelationSymbol)
			return false;
		return true;
	}

	public static MultiIndexArrayUpdate of(final Script script, final Term term) {
		final BinaryEqualityRelation ber = BinaryEqualityRelation.convert(term);
		if (ber == null) {
			return null;
		}
		if (!SmtSortUtils.isArraySort(ber.getLhs().getSort())) {
			return null;
		}
		final MultiDimensionalNestedStore mdnsLhs = MultiDimensionalNestedStore.of(ber.getLhs());
		final MultiDimensionalNestedStore mdnsRhs = MultiDimensionalNestedStore.of(ber.getRhs());
		if (mdnsRhs != null && mdnsLhs == null) {
			return new MultiIndexArrayUpdate(ber.getRelationSymbol(), ber.getLhs(), mdnsRhs);
		} else if (mdnsLhs != null && mdnsRhs == null) {
			return new MultiIndexArrayUpdate(ber.getRelationSymbol(), ber.getRhs(), mdnsLhs);
		} else {
			return null;
		}
	}

	@Override
	public String toString() {
		return String.format("(%s %s %s)", mRelationSymbol, mNewArray, mMultiDimensionalNestedStore);
	}

	@Override
	public Term toTerm(final Script script) {
		return mRelationSymbol.constructTerm(script, mNewArray, mMultiDimensionalNestedStore.toTerm(script));
	}

}
