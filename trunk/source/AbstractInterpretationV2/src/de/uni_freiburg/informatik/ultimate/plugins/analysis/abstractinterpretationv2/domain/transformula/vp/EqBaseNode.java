package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqBaseNode extends EqNode {
	
	private final IProgramVarOrConst mVarOrConst;
	private final boolean mIsLiteral;

	public EqBaseNode(IProgramVarOrConst bv) {
		mVarOrConst = bv;
		mIsLiteral = bv.getTerm() instanceof ConstantTerm;
	}
	
	public String toString() {
		return mVarOrConst.toString();
	}

	@Override
	public Term getTerm(Script s) {
		return mVarOrConst.getTerm();
	}
	
	@Override
	public boolean isLiteral() {
		return mIsLiteral;
	}

	@Override
	public boolean equals(Object other) {
		return other == this;
//		if (!(other instanceof EqBaseNode)) {
//			return false;
//		}
//		EqBaseNode ebn = (EqBaseNode) other;
//		
//		return ebn.mBoogieVarOrConst.equals(this.mBoogieVarOrConst);
	}
}
