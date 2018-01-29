package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

/**
 * Wrapper for an IcfgEdge that carries information about the edge that we are interested in in the heap separator.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
class EdgeInfo {
	IcfgEdge mEdge;

	EdgeInfo(final IcfgEdge edge) {
		mEdge = edge;
	}

	public IProgramVarOrConst getProgramVarOrConstForTerm(final Term term) {
		return TransFormulaUtils.getProgramVarOrConstForTerm(mEdge.getTransformula(), term);
	}

	public IcfgLocation getSourceLocation() {
		return mEdge.getSource();
	}

	public IcfgEdge getEdge() {
		return mEdge;
	}

	@Override
	public String toString() {
		return "(" + mEdge + ")";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mEdge == null) ? 0 : mEdge.hashCode());
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
		final EdgeInfo other = (EdgeInfo) obj;
		if (mEdge == null) {
			if (other.mEdge != null) {
				return false;
			}
		} else if (!mEdge.equals(other.mEdge)) {
			return false;
		}
		return true;
	}
}