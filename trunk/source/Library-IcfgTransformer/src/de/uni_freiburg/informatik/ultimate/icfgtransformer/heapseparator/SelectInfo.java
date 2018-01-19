package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

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

	public SelectInfo(final ArrayCellAccess arrayCellAccess, final EdgeInfo edgeInfo) {
		super();
		mArrayCellAccess = arrayCellAccess;
		mEdgeInfo = edgeInfo;
	}

	public ArrayCellAccess getArrayCellAccess() {
		return mArrayCellAccess;
	}

	public EdgeInfo getEdgeInfo() {
		return mEdgeInfo;
	}

	public IProgramVarOrConst getArrayPvoc() {
		return getEdgeInfo().getProgramVarOrConstForTerm(getArrayCellAccess().getArray());
	}


}
