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

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a store term somewhere in the program and the location in the program where that
 * store happens; colloquially: a "write location".
 *
 * A StoreInfo is identified by a {@link SubtreePosition} and an {@link EdgeInfo}. (It represents the store term at that
 * position in the edge's transition formula.)
 *
 * A write location has the following properties:
 * <ul>
 *  <li> the program location it occurs in
 *  <li> the store term that does the "write" to the array
 *  <li> the (program-level) {@link ArrayGroup} that is concerned (i.e. both the base array of the store term and the
 *    array on the other side of the equation belong to it)
 *  <li> if the store term is inside a multidimensional write (i.e., if it's array is not a TermVariable but a select
 *       term):  <br>
 *       the indices in the enclosing store terms (in a {@link MultiDimensionalStore}, the normal case, they coincide
 *       with the indices of the select term used to access the array, but we do not assume/require that)
 *  <li> the index term of the store
 * </ul>
 * The last three parameters are extracted from the store term for convenience. The "value" argument of the store term
 *  (which may contain another store) is ignored.
 *
 * (Note that a storeInfo is not identified only by the program location and the store term. That store Term may appear
 *    in many places in the TransFormula! In particular the enclosing indices may change. We want a different StoreInfo
 *    for each occurrence of that store Term in that TransFormula!)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class StoreInfo {

	private final EdgeInfo mEdgeInfo;

	private final Term mStoreTerm;

	private final ArrayGroup mArrayGroup;

	private final ArrayIndex mEnclosingIndices;

	private final Term mStoreIndex;

	/**
	 * StoreIndexInfos are unified by a map in {@link StoreIndexFreezerIcfgTransformer}.
	 * They are given an id at construction, we use this for equals and hashcode, too.
	 * <p>
	 * Conceptually, a StoreInfo is determined by {@link #mEdgeInfo} and {@link #mStoreTerm}.
	 */
	private final int mId;

	private final IProgramConst mLocLit;

	private final SubtreePosition mSubtreePosition;

	private final ArrayEqualityLocUpdateInfo mEnclosingEquality;

	private final SubtreePosition mPositionOfStoredValueRelativeToEquality;


	/**
	 *
	 * @param edgeInfo
	 * @param storeTerm
	 * @param id
	 * @param subTreePosition
	 * @param enclosingIndices
	 * @param iProgramConst
	 */
	public StoreInfo(final int id, final EdgeInfo edgeInfo, final SubtreePosition subTreePosition,
			final Term storeTerm, final ArrayGroup array, final ArrayIndex enclosingIndices,
			final IProgramConst locLit, final ArrayEqualityLocUpdateInfo enclosingEquality,
			final SubtreePosition posRelativeToEquality) {
		assert this instanceof NoStoreInfo ||
			(Objects.nonNull(edgeInfo) &&
					Objects.nonNull(storeTerm) &&
					Objects.nonNull(array) &&
					Objects.nonNull(locLit) &&
					id >= 0);

		mEdgeInfo = edgeInfo;
		mSubtreePosition = subTreePosition;
		mStoreTerm = storeTerm;
		mArrayGroup = array;
		mEnclosingIndices = enclosingIndices;
		mLocLit = locLit;
		mEnclosingEquality = enclosingEquality;

		// need to append, be cause the given position is that of the store term
		if (this instanceof NoStoreInfo) {
			mPositionOfStoredValueRelativeToEquality = null;

			mStoreIndex = null;
		} else {
			mPositionOfStoredValueRelativeToEquality = posRelativeToEquality.append(2);

			assert mEnclosingEquality != null;

			assert SmtUtils.isFunctionApplication(storeTerm, "store") : "expecting store term";

			mEnclosingEquality.addEnclosedStoreInfo(this, posRelativeToEquality);

			{
				final ApplicationTerm at = (ApplicationTerm) storeTerm;
				final Term stIndex = at.getParameters()[1];

				mStoreIndex = stIndex;
			}
		}
		mId = id;
	}

	public EdgeInfo getEdgeInfo() {
		return mEdgeInfo;
	}

	public Term getStoreTerm() {
		return mStoreTerm;
	}

	public Term getStoreIndex() {
		return mStoreIndex;
	}

	/**
	 * The store term of this store info may be enclosed inside multidimensional store. This stores the indices of the
	 * enclosing stores.
	 * <p>
	 * See also {@link StoreInfo}.
	 * @return
	 */
	public ArrayIndex getEnclosingIndices() {
		return mEnclosingIndices;
	}

	/**
	 * @return The array group that is concerned by the store.
	 */
	public ArrayGroup getArrayGroup() {
		return mArrayGroup;
	}

	/**
	 * Dimension at which this store accesses the base array (i.e., the outermost array-type expression it occurs in)
	 *
	 * Example for convention how we count: a[i] is a read at dimension 1, x is a read at dimension 0, a[i, j] at 2
	 *
	 * @return
	 */
	public Integer getDimension() {
		return mEnclosingIndices.size() + 1;
	}

	@Override
	public String toString() {
		return "(Store [" + mId + "] at" + mEdgeInfo + " with " + mStoreTerm + ")";
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
		final StoreInfo other = (StoreInfo) obj;
		if (mId != other.mId) {
			return false;
		}
		return true;
	}

	public IProgramConst getLocLiteral() {
		return mLocLit;
	}

	public int getId() {
		return mId;
	}

	/**
	 * Determine if this store is "top-level", i.e., it is not inside another store.
	 *
	 * @return
	 */
	public boolean isOutermost() {
		return getDimension() == 1;
	}

	public SubtreePosition getPositionOfStoredValueRelativeToEquality() {
		return mPositionOfStoredValueRelativeToEquality;
	}

	/**
	 * Tree position of the mStoreTerm in mEdgeInfo's formula.
	 * @return
	 */
	public SubtreePosition getPosition() {
		return mSubtreePosition;
	}

	/**
	 * unclear if this method is needed or if we can just use the constructor..
	 *
	 * @param siId
	 * @param edge
	 * @param subTreePosition
	 * @param term
	 * @param arrayGroup
	 * @param enclosingStoreIndices
	 * @param locLit
	 * @return
	 */
	public static StoreInfo buildStoreInfo(final int siId, final EdgeInfo edge,
			final SubtreePosition subTreePosition, final ApplicationTerm term, final ArrayGroup arrayGroup,
			final ArrayIndex enclosingStoreIndices, final IProgramConst locLit,
			final ArrayEqualityLocUpdateInfo enclosingEquality, final SubtreePosition posRelativeToOutermost) {
		return new StoreInfo(siId, edge, subTreePosition, term, arrayGroup, enclosingStoreIndices, locLit,
				enclosingEquality, posRelativeToOutermost);
	}
}