/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * {@link ITermProvider} for the (rather complex) select over store, where we
 * have multiple dimensions and nested stores.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class MultiDimensionalSelectOverNestedStore implements ITermProvider {

	private final ArrayIndex mSelectIndex;
	private final MultiDimensionalNestedStore mNestedStore;

	public MultiDimensionalSelectOverNestedStore(final ArrayIndex selectIndex,
			final MultiDimensionalNestedStore nestedStore) {
		super();
		if (selectIndex.size() != nestedStore.getDimension()) {
			throw new IllegalArgumentException("Incompatible dimensions");
		}
		mSelectIndex = selectIndex;
		mNestedStore = nestedStore;
	}

	public ArrayIndex getSelectIndex() {
		return mSelectIndex;
	}

	public MultiDimensionalNestedStore getNestedStore() {
		return mNestedStore;
	}

	@Override
	public Term toTerm(final Script script) {
		return new MultiDimensionalSelect(mNestedStore.toTerm(script), mSelectIndex).toTerm(script);
	}

	public static MultiDimensionalSelectOverNestedStore of(final Term term) {
		final MultiDimensionalSelect mds = MultiDimensionalSelect.of(term);
		if (mds == null) {
			return null;
		}
		final MultiDimensionalNestedStore mdns = MultiDimensionalNestedStore.of(mds.getArray());
		if (mdns == null) {
			return null;
		}
		if (mds.getDimension() != mdns.getDimension()) {
			return null;
		}
		return new MultiDimensionalSelectOverNestedStore(mds.getIndex(), mdns);
	}

	/**
	 * @return Term that is equivalent to this
	 *         {@link MultiDimensionalSelectOverNestedStore} if the index of the
	 *         select and the index of each store are distinct.
	 */
	public Term constructNotEqualsReplacement(final Script script) {
		final MultiDimensionalSelect mds = new MultiDimensionalSelect(getNestedStore().getArray(), getSelectIndex());
		return mds.toTerm(script);
	}

	/**
	 *
	 * @return List of all {@link MultiDimensionalSelectOverNestedStore} that occur
	 *         in given term.
	 */
	public static List<MultiDimensionalSelectOverNestedStore> extractMultiDimensionalSelectOverNestedStore(
			final Term term, final boolean onlyOutermost) {
		final List<MultiDimensionalSelectOverNestedStore> result = new ArrayList<>();
		final List<MultiDimensionalSelect> mdss = MultiDimensionalSelect.extractSelectShallow(term);
		for (final MultiDimensionalSelect mds : mdss) {
			final MultiDimensionalNestedStore mdns = MultiDimensionalNestedStore.of(mds.getArray());
			if (mdns != null) {
				result.add(new MultiDimensionalSelectOverNestedStore(mds.getIndex(), mdns));
				if (!onlyOutermost) {
					result.addAll(extractMultiDimensionalSelectOverNestedStore(mdns.getArray(), onlyOutermost));
					for (int i = 0; i < mdns.getIndices().size(); i++) {
						result.addAll(
								extractMultiDimensionalSelectOverNestedStore(mdns.getValues().get(i), onlyOutermost));
						for (int j = 0; j < mdns.getDimension(); j++) {
							final Term indexEntry = mdns.getIndices().get(i).get(j);
							result.addAll(extractMultiDimensionalSelectOverNestedStore(indexEntry, onlyOutermost));
						}
					}

				}
			} else {
				// no MultiDimensionalNestedStore inside or MultiDimensionalNestedStore not
				// compatible
				result.addAll(extractMultiDimensionalSelectOverNestedStore(mds.getArray(), onlyOutermost));
				for (final Term entry : mds.getIndex()) {
					result.addAll(extractMultiDimensionalSelectOverNestedStore(entry, onlyOutermost));
				}
			}
		}
		return result;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mNestedStore == null) ? 0 : mNestedStore.hashCode());
		result = prime * result + ((mSelectIndex == null) ? 0 : mSelectIndex.hashCode());
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
		final MultiDimensionalSelectOverNestedStore other = (MultiDimensionalSelectOverNestedStore) obj;
		if (mNestedStore == null) {
			if (other.mNestedStore != null)
				return false;
		} else if (!mNestedStore.equals(other.mNestedStore))
			return false;
		if (mSelectIndex == null) {
			if (other.mSelectIndex != null)
				return false;
		} else if (!mSelectIndex.equals(other.mSelectIndex))
			return false;
		return true;
	}

}
