package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Represents an index that is used in a store term somewhere in the program.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StoreIndexInfo {
	private final EdgeInfo mEdgeInfo;
	private final Term mTerm;

	/**
	 * Each array write happens at a certain dimension of ore or more arrays.
	 *  (+ the same Term may be used to do more than one array write in an IcfgEdge)
	 *
	 * which array is written at which dimensions in the given edge with the given term
	 */
	private final HashRelation<IProgramVarOrConst, Integer> mArrayToAccessDimensions;

	private final Set<Integer> mAccessDimensions;

	/**
	 * StoreIndexInfos are unified by a map in {@link StoreIndexFreezerIcfgTransformer}.
	 * They are given an id at construction, we use this for equals and hashcode, too.
	 */
	private final int mId;

	/**
	 *
	 * @param edgeInfo
	 * @param term
	 * @param storeIndexInfoCounter
	 */
	public StoreIndexInfo(final EdgeInfo edgeInfo, final Term term, final int storeIndexInfoCounter) {
		super();
		mEdgeInfo = edgeInfo;
		mTerm = term;
		mArrayToAccessDimensions = new HashRelation<>();// = computeArrayToAccessDimensions(edgeInfo, term);
		mAccessDimensions = new HashSet<>();
		mId = storeIndexInfoCounter;
	}

//	private HashRelation<IProgramVarOrConst, Integer> computeArrayToAccessDimensions(final EdgeInfo edgeInfo, final Term term) {
//		final ApplicationTermFinder atf = new
//		for (SmtUtils.find)
//		// TODO Auto-generated method stub
//		return null;
//	}

	public void addArrayAccessDimension(final IProgramVarOrConst array, final Integer accessDimension) {
		mArrayToAccessDimensions.addPair(array, accessDimension);
		mAccessDimensions.add(accessDimension);
	}

	public EdgeInfo getEdgeInfo() {
		return mEdgeInfo;
	}

	public Term getIndexTerm() {
		return mTerm;
	}

	public Set<Integer> getAccessDimensions() {
		return Collections.unmodifiableSet(mAccessDimensions);
	}

	/**
	 *
	 * @return all the arrays that the stores with mTerm refer to in mEdgeInfo.
	 */
	public Set<IProgramVarOrConst> getArrays() {
		return mArrayToAccessDimensions.getDomain();
	}

	public HashRelation<IProgramVarOrConst, Integer> getArrayToAccessDimensions() {
		return mArrayToAccessDimensions;
	}

	@Override
	public String toString() {
		return "(Store [" + mId + "] at" + mEdgeInfo + " with " + mTerm + ")";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + mId;
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
		final StoreIndexInfo other = (StoreIndexInfo) obj;
		if (mId != other.mId) {
			return false;
		}
		return true;
	}

	public int getId() {
		return mId;
	}

//	@Override
//	public int hashCode() {
//		final int prime = 31;
//		int result = 1;
//		result = prime * result + ((mEdgeInfo == null) ? 0 : mEdgeInfo.hashCode());
//		result = prime * result + ((mTerm == null) ? 0 : mTerm.hashCode());
//		return result;
//	}
//
//	@Override
//	public boolean equals(final Object obj) {
//		if (this == obj) {
//			return true;
//		}
//		if (obj == null) {
//			return false;
//		}
//		if (getClass() != obj.getClass()) {
//			return false;
//		}
//		final StoreIndexInfo other = (StoreIndexInfo) obj;
//		if (mEdgeInfo == null) {
//			if (other.mEdgeInfo != null) {
//				return false;
//			}
//		} else if (!mEdgeInfo.equals(other.mEdgeInfo)) {
//			return false;
//		}
//		if (mTerm == null) {
//			if (other.mTerm != null) {
//				return false;
//			}
//		} else if (!mTerm.equals(other.mTerm)) {
//			return false;
//		}
//		return true;
//	}
//



}

/**
 * special dummy store index info that stands for the absence of any relevant array writes at some read location
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
class NoStoreIndexInfo extends StoreIndexInfo {

	public NoStoreIndexInfo() {
		super(null, null, -1);
	}

//	@Override
//	public int hashCode() {
//		return 0;
//	}
//
//	@Override
//	public boolean equals(final Object obj) {
//		if (this == obj) {
//			return true;
//		}
//		if (obj == null) {
//			return false;
//		}
//		if (getClass() != obj.getClass()) {
//			return false;
//		}
//		return true;
//	}

	@Override
	public String toString() {
		return "NoStoreIndexInfo";
	}
}