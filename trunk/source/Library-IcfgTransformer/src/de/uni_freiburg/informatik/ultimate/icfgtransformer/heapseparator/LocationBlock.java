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
}
