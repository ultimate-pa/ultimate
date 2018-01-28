package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

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

	private final List<Term> mNormalizedArrayIndex;

	public SelectInfo(final ArrayCellAccess arrayCellAccess, final EdgeInfo edgeInfo, final ManagedScript mgdScript) {
		super();
		mArrayCellAccess = arrayCellAccess;
		mEdgeInfo = edgeInfo;
		mNormalizedArrayIndex = VPDomainHelpers.normalizeArrayIndex(arrayCellAccess.getIndex(),
				edgeInfo.getEdge().getTransformula(), mgdScript);
	}

//	public ArrayCellAccess getArrayCellAccess() {
//		return mArrayCellAccess;
//	}

	public EdgeInfo getEdgeInfo() {
		return mEdgeInfo;
	}

	public IProgramVarOrConst getArrayPvoc() {
		return getEdgeInfo().getProgramVarOrConstForTerm(mArrayCellAccess.getSimpleArray());
	}

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

	public Term getNormalizedArrayIndex(final int dim) {
		return mNormalizedArrayIndex.get(dim);
	}


}
