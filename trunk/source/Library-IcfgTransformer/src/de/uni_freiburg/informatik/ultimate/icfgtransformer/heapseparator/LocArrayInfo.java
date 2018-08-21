package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class LocArrayInfo {

	private final EdgeInfo mEdge;
	private final IProgramVarOrConst mPvoc;
	private final Term mTerm;
	private final Term mInitializingConstantArray;

	public LocArrayInfo(final EdgeInfo edge, final IProgramVarOrConst pvoc, final Term term,
			final Term initializingConstantArray) {
		mEdge = edge;
		mPvoc = pvoc;
		mTerm = term;
		mInitializingConstantArray = initializingConstantArray;
	}

	public IProgramVarOrConst getPvoc() {
		return mPvoc;
	}

	public Term getTerm() {
		return mTerm;
	}

	public Term getInitializingConstantArray() {
		return mInitializingConstantArray;
	}
}