package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class VPArrayIdentifier {
	
	IProgramVarOrConst mPvoc;
	Term mTerm;
	
//	public VPArrayIdentifier(IProgramVarOrConst pvoc) {
//		mPvoc = pvoc;
//	}

	public VPArrayIdentifier(Term term) {
		assert term != null;
		mTerm = term;
	}

	@Override
	public boolean equals(Object other) {
		if (!(other instanceof VPArrayIdentifier)) {
			return false;
		}
		VPArrayIdentifier otherArrayId = (VPArrayIdentifier) other;
		return this.mTerm == otherArrayId.mTerm && this.mPvoc == otherArrayId.mPvoc;
	}
	
	@Override
	public String toString() {
		if (mPvoc != null) {
			return "ArrayId: " + mPvoc.toString();
		}
		if (mTerm != null) {
			return "ArrayId: " + mTerm.toString();
		}
		assert false;
		return null;
	}

	@Override
	public int hashCode() {
		// TODO
		return 0;
	}
	
}
