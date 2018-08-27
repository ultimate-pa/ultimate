package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class LocArrayInfo {

	private final EdgeInfo mEdge;
	private final IProgramVarOrConst mPvoc;
	private final Term mTerm;
	private final Term mInitializingConstantArray;

	/**
	 *
	 * Note: the term is not the term from the pvoc (even if it exists)
	 *
	 * @param edge
	 * @param pvoc
	 * @param term
	 * @param initializingConstantArray
	 */
	public LocArrayInfo(final EdgeInfo edge, final IProgramVarOrConst pvoc, final Term term,
			final Term initializingConstantArray) {
		mEdge = edge;
		mPvoc = pvoc;
		mTerm = term;
		assert this instanceof LocArrayReadInfo || initializingConstantArray != null;
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

	public boolean isGlobalPvoc() {
		return mPvoc != null && mPvoc instanceof IProgramNonOldVar;
	}
}