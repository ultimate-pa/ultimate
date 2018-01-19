package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Collections;
import java.util.Set;

/**
 * relative to an array group, also can give the subarray for each array in the array group that corresponds to teh
 * location block
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class LocationBlock {
//	Set<IProgramVarOrConst> mAssociatedArrayGroup;
	ArrayGroup mAssociatedArrayGroup;

//	Map<IProgramVar, IProgramVar> arrayToSubarray;

	private final Set<StoreIndexInfo> mLocations;

	public LocationBlock(final Set<StoreIndexInfo> eqc, final ArrayGroup associatedArrayGroup) {
		mLocations = Collections.unmodifiableSet(eqc);
		mAssociatedArrayGroup = associatedArrayGroup;
	}


}
