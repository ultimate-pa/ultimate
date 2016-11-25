package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class BoogieVarOrConst implements IProgramVarOrConst {
	
	final bvocType mType;
	
	final Term mTerm;
	
	final IProgramVar mProgramVar;

	final ConstantTerm mConstantTerm;
	
	final BoogieConst mBoogieConst;
	
	public BoogieVarOrConst(IProgramVar pv) {
		mType = bvocType.PROGRAMVAR;
		mTerm = pv.getTerm();
		mProgramVar = pv;
		mConstantTerm = null;
		mBoogieConst = null;
	}
	
	public BoogieVarOrConst(BoogieConst bc) {
		mType = bvocType.BOOGIECONST;
		mTerm = bc.getTerm();
		mProgramVar = null;
		mConstantTerm = null;
		mBoogieConst = bc;
	}

	public BoogieVarOrConst(ConstantTerm ct) {
		mType = bvocType.CONST;
		mTerm = ct;
		mProgramVar = null;
		mConstantTerm = ct;
		mBoogieConst = null;
	}
	
	@Override
	public String getGloballyUniqueId() {
		switch (mType) {
		case BOOGIECONST:
			return mBoogieConst.getGloballyUniqueId();
		case CONST:
			return mConstantTerm.toString();
		case PROGRAMVAR:
			return mProgramVar.getGloballyUniqueId();
		default:
			assert false;
			return null;
		}
	}

	@Override
	public Term getTerm() {
		return mTerm;
	}
	
	@Override
	public String toString() {
		return mTerm.toString();
	}
	
	private enum bvocType { PROGRAMVAR, BOOGIECONST, CONST };
}
