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
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Represents an index that is used in a store term somewhere in the program and the location in the program where that
 * store happens; colloquially: a "write location".
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StoreIndexInfo {
	private final EdgeInfo mEdgeInfo;
	private final Term mTerm;

	/**
	 * Each array write happens at a certain dimension of one or more arrays.
	 *  (+ the same Term may be used to do more than one array write in an IcfgEdge)
	 * <p>
	 * This map stores which array is written at which dimensions in the given edge with the given term.
	 * <p>
	 * Storing the accessed dimensions allows an optimization when we compute the conjunction over elements of the cross
	 *  product of partition blocks -- we may leave out certain blocks at certain positions in the cross product if we
	 *  know none of their elements can ever be relevant at the given dimension.
	 * Note that this is only an optimization and not conceptually relevant as it drops conjuncts that would be
	 *  redundant anyway.
	 */
//	private final HashRelation<IProgramVarOrConst, Integer> mArrayToAccessDimensions;
	private final HashRelation<ArrayGroup, Integer> mArrayToAccessDimensions;

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

//	public void addArrayAccessDimension(final IProgramVarOrConst array, final Integer accessDimension) {
	public void addArrayAccessDimension(final ArrayGroup array, final Integer accessDimension) {
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
//	public Set<IProgramVarOrConst> getArrays() {
	public Set<ArrayGroup> getArrays() {
		return mArrayToAccessDimensions.getDomain();
	}

//	public HashRelation<IProgramVarOrConst, Integer> getArrayToAccessDimensions() {
	public HashRelation<ArrayGroup, Integer> getArrayToAccessDimensions() {
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