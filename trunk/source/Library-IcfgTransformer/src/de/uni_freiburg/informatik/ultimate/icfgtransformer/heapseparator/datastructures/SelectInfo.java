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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Represents a select term somewhere in the program.
 *  (including its location in the program)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class SelectInfo {

	private final ArrayCellAccess mArrayCellAccess;

	private final EdgeInfo mEdgeInfo;

	private final ArrayGroup mArrayGroup;

	public SelectInfo(final ArrayCellAccess arrayCellAccess, final EdgeInfo edgeInfo, final ArrayGroup arrayGroup,
			final ManagedScript mgdScript) {
		super();
		mArrayCellAccess = arrayCellAccess;
		mEdgeInfo = edgeInfo;
		mArrayGroup = arrayGroup;
	}

//	public ArrayCellAccess getArrayCellAccess() {
//		return mArrayCellAccess;
//	}

	public EdgeInfo getEdgeInfo() {
		return mEdgeInfo;
	}

//	/**
//	 *
//	 * deprecated because array may not have a pvoc (i.e. be an auxvar)
//	 *
//	 * @return
//	 */
//	@Deprecated
//	public IProgramVarOrConst getArrayPvoc() {
//		return getEdgeInfo().getProgramVarOrConstForTerm(mArrayCellAccess.getSimpleArray());
//	}

	@Override
	public String toString() {
		return "(" + mArrayCellAccess + ", at " + mEdgeInfo + ")";
	}

	public ArrayIndex getIndex() {
		return mArrayCellAccess.getIndex();
	}

	public ArrayCellAccess getArrayCellAccess() {
		return mArrayCellAccess;
	}

	public ArrayGroup getArrayGroup() {
		return mArrayGroup;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mArrayCellAccess == null) ? 0 : mArrayCellAccess.hashCode());
		result = prime * result + ((mEdgeInfo == null) ? 0 : mEdgeInfo.hashCode());
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
		final SelectInfo other = (SelectInfo) obj;
		if (mArrayCellAccess == null) {
			if (other.mArrayCellAccess != null) {
				return false;
			}
		} else if (!mArrayCellAccess.equals(other.mArrayCellAccess)) {
			return false;
		}
		if (mEdgeInfo == null) {
			if (other.mEdgeInfo != null) {
				return false;
			}
		} else if (!mEdgeInfo.equals(other.mEdgeInfo)) {
			return false;
		}
		return true;
	}
}
