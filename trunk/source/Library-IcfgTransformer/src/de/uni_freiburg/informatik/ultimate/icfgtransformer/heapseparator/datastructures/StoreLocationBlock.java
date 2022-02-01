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

import java.util.Collections;
import java.util.Set;

/**
 * Represents a set of array write locations (which are represented by the class {@link StoreInfo}. An array write
 *  location consists of a program location, represented by an IcfgEdge or an EdgeInfo instance, and a Term that is used
 *  as index of the written array cell in the IcfgEdge.
 *
 * Relative to an array group; also can give the subarray for each array in the array group that corresponds to the
 * location block
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StoreLocationBlock {

	/**
	 * This LocationBlock considers writes only to arrays in mArrayGroup
	 */
	private final ArrayGroup mArrayGroup;

	/**
	 * This LocationBlock considers writes only to arrays at dimension mDimension in mArrayGroup.
	 */
	private final int mDimension;

	private final Set<StoreInfo> mStoreInfos;

	public StoreLocationBlock(final Set<StoreInfo> eqc, final ArrayGroup associatedArrayGroup, final int dimension) {
		mStoreInfos = Collections.unmodifiableSet(eqc);
		mArrayGroup = associatedArrayGroup;
		mDimension = dimension;
	}

	public boolean contains(final StoreInfo sii) {
		return mStoreInfos.contains(sii);
	}

	@Override
	public String toString() {
		return "locs_" + (mStoreInfos.hashCode() % 100);
	}

	public Set<StoreInfo> getLocations() {
		return mStoreInfos;
	}

	public ArrayGroup getArrayGroup() {
		return mArrayGroup;
	}

	public int getDimension() {
		return mDimension;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mArrayGroup == null) ? 0 : mArrayGroup.hashCode());
		result = prime * result + mDimension;
		result = prime * result + ((mStoreInfos == null) ? 0 : mStoreInfos.hashCode());
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
		final StoreLocationBlock other = (StoreLocationBlock) obj;
		if (mArrayGroup == null) {
			if (other.mArrayGroup != null) {
				return false;
			}
		} else if (!mArrayGroup.equals(other.mArrayGroup)) {
			return false;
		}
		if (mDimension != other.mDimension) {
			return false;
		}
		if (mStoreInfos == null) {
			if (other.mStoreInfos != null) {
				return false;
			}
		} else if (!mStoreInfos.equals(other.mStoreInfos)) {
			return false;
		}
		return true;
	}
}
