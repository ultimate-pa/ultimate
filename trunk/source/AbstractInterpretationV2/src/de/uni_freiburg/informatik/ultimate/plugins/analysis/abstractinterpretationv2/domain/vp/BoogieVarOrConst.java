package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class BoogieVarOrConst {
	
	final bvocType mType;
	
	final Term mTerm;
	
	public BoogieVarOrConst(IProgramVar pv) {
		mType = bvocType.PROGRAMVAR;
		mTerm = pv.getTermVariable();
	}
	
	public BoogieVarOrConst(BoogieConst bc) {
		mType = bvocType.BOOGIECONST;
		mTerm = bc.getDefaultConstant();
	}

	public BoogieVarOrConst(ConstantTerm ct) {
		mType = bvocType.CONST;
		mTerm = ct;
	}
	
	public Term getTerm() {
		return mTerm;
	}
	
	@Override
	public String toString() {
		return mTerm.toString();
	}
	
	private enum bvocType { PROGRAMVAR, BOOGIECONST, CONST };
}
