package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a loc-array.
 * Each loc-array corresponds to one array-term (typically a TermVariable) in some IcfgEdge.
 * The array-term may or may not be related to an {@link IProgramVarOrConst} (it is, if it belongs to an in var or out
 * var in the given edge).
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class LocArrayInfo {

	private final EdgeInfo mEdge;
	private final IProgramVarOrConst mPvoc;
	private final Term mTerm;
	private final Term mInitializingConstantArray;

	/**
	 *
	 * See {@link LocArrayInfo}
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

	public EdgeInfo getEdge() {
		return mEdge;
	}
}