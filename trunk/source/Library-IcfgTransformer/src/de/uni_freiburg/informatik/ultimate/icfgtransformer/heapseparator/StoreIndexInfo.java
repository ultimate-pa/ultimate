package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

/**
 * Represents an index that is used in a store term somewhere in the program.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StoreIndexInfo {
	private final EdgeInfo mEdgeInfo;
	private final Term mTerm;

	public StoreIndexInfo(final EdgeInfo edgeInfo, final Term term) {
		super();
		mEdgeInfo = edgeInfo;
		mTerm = term;
	}

	public EdgeInfo getEdgeInfo() {
		return mEdgeInfo;
	}

	public Term getTermVariable() {
		return mTerm;
	}
}

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

	public IProgramVarOrConst getProgramVarOrConstForTerm(final Term array) {
		// TODO Auto-generated method stub
		return null;
	}

//	public IProgramVarOrConst getPvoc(final Term array) {
//		// TODO Auto-generated method stub
//		return null;
//	}

}
