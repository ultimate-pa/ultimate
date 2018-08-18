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

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;

/**
 * Represents a store term somewhere in the program and the location in the program where that
 * store happens; colloquially: a "write location".
 *
 * A write location has the following properties:
 * <ul>
 *  <li> the program location it occurs in
 *  <li> the store term that does the "write" to the array
 *  <li> the array that is written to
 *  <li> if the store term is inside a multidimensional write (i.e., if it's array is not a TermVariable but a select
 *       term):  <br>
 *       the indices in the enclosing store terms (in a {@link MultiDimensionalStore}, the normal case, they coincide
 *       with the indices of the select term used to access the array, but we do not assume/require that)
 *  <li> the index term of the store
 * </ul>
 * The last three parameters are extracted from the store term for convenience. The "value" argument of the store term
 *  (which may contain another store) is ignored.
 *
 *  EDIT:
 *   Note that a storeInfo is not identified only by the program location and the store term. That store Term may appear
 *    in many places in the TransFormula! In particular the enclosing indices may change. We want a different StoreInfo
 *    for each occurrence of that store Term in that TransFormula!
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
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

	/**
	 *
	 * @param edgeInfo
	 * @param storeTerm
	 * @param id
	 * @param enclosingIndices
	 * @param iProgramConst
	 */
	public StoreInfo(final int id, final EdgeInfo edgeInfo, final Term storeTerm, final ArrayGroup array,
			final ArrayIndex enclosingIndices, final IProgramConst locLit) {
		assert this instanceof NoStoreInfo ||
			(Objects.nonNull(edgeInfo) &&
					Objects.nonNull(storeTerm) &&
					Objects.nonNull(array) &&
					Objects.nonNull(locLit) &&
					id >= 0);
		mEdgeInfo = edgeInfo;
		mStoreTerm = storeTerm;
		mArrayGroup = array;
		mEnclosingIndices = enclosingIndices;
		mLocLit = locLit;

		assert SmtUtils.isFunctionApplication(storeTerm, "store") : "expecting store term";

		{
			final ApplicationTerm at = (ApplicationTerm) storeTerm;
//			final Term stArray = at.getParameters()[0];
			final Term stIndex = at.getParameters()[1];

//			final MultiDimensionalSelect mdSel = new MultiDimensionalSelect(stArray);
//			mEnclosingIndices = mdSel.getIndex();

			mStoreIndex = stIndex;
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
	 * If the array in the store term (its first argument) is a (multidimensional) select, this stores its index.
	 * EDIT: that is wrong in general.
	 * See {@link StoreInfo}
	 * @return
	 */
	public ArrayIndex getEnclosingIndices() {
		return mEnclosingIndices;
	}

	/**
	 *
	 * @return
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

	public int getId() {
		return mId;
	}
}