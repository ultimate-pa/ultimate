package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class VPArrayIdentifier {
	
	IProgramVarOrConst mPvoc;
	Term mTerm;
	
	public VPArrayIdentifier(IProgramVarOrConst pvoc) {
		mPvoc = pvoc;
	}

	public VPArrayIdentifier(Term term) {
		mTerm = term;
	}

}
