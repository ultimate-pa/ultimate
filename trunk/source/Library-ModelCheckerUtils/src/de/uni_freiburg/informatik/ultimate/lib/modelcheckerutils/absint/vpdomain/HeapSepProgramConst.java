package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a "freeze var literal" in the sense of the freeze var style preprocessing in the heap separator
 * IcfgTransformation.
 *
 * Not clear if this class is the best solution.
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HeapSepProgramConst implements IProgramConst {

	/**
	 *
	 */
	private static final long serialVersionUID = 1351754672207744404L;

	private final ApplicationTerm mDefaultConstant;
	private final String mGloballyUniqueId;

	public HeapSepProgramConst(final ApplicationTerm term) {
		mDefaultConstant = term;
		mGloballyUniqueId = term.toString();
	}

	@Override
	public Term getTerm() {
		return getDefaultConstant();
	}

	@Override
	public boolean isGlobal() {
		return true;
	}

	@Override
	public String getGloballyUniqueId() {
		return mGloballyUniqueId;
	}

	@Override
	public String getIdentifier() {
		return getGloballyUniqueId();
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		return mDefaultConstant;
	}

	@Override
	public String toString() {
		return getGloballyUniqueId();
	}
}
