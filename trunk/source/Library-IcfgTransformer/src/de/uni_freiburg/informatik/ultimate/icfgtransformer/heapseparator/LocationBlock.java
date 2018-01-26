package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Collections;
import java.util.Set;

/**
 * Represents a set of array write locations (which are represented by the class {@link StoreIndexInfo}. An array write
 *  location consists of a program location, represented by an IcfgEdge or an EdgeInfo instance, and a Term that is used
 *  as index of the written array cell in the IcfgEdge.
 *
 * Relative to an array group; also can give the subarray for each array in the array group that corresponds to the
 * location block
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class LocationBlock {
//	Set<IProgramVarOrConst> mAssociatedArrayGroup;

	/**
	 * This LocationBlock considers writes only to arrays in mArrayGroup
	 */
	private final ArrayGroup mArrayGroup;

	/**
	 * This LocationBlock considers writes only to arrays at dimension mDimension in mArrayGroup.
	 */
	private final int mDimension;

	private final Set<StoreIndexInfo> mStoreIndexInfos;

//	private final Set<Integer> mArrayAccessDimensions;

	public LocationBlock(final Set<StoreIndexInfo> eqc, final ArrayGroup associatedArrayGroup, final int dimension) {
		mStoreIndexInfos = Collections.unmodifiableSet(eqc);
		mArrayGroup = associatedArrayGroup;
		mDimension = dimension;

//		mArrayAccessDimensions = new HashSet<>();
//		for (final StoreIndexInfo sii : eqc) {
//			mArrayAccessDimensions.addAll(sii.getAccessDimensions());
//		}
	}

	public boolean contains(final StoreIndexInfo sii) {
		return mStoreIndexInfos.contains(sii);
	}

//	public Set<Integer> getAccessDimensions() {
//		return Collections.unmodifiableSet(mArrayAccessDimensions);
//	}

	@Override
	public String toString() {
		return "locs_" + (mStoreIndexInfos.hashCode() % 100);
	}

	public Set<StoreIndexInfo> getLocations() {
		return mStoreIndexInfos;
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
		result = prime * result + ((mStoreIndexInfos == null) ? 0 : mStoreIndexInfos.hashCode());
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
		final LocationBlock other = (LocationBlock) obj;
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
		if (mStoreIndexInfos == null) {
			if (other.mStoreIndexInfos != null) {
				return false;
			}
		} else if (!mStoreIndexInfos.equals(other.mStoreIndexInfos)) {
			return false;
		}
		return true;
	}


}
