package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqBaseNode extends EqNode {
	
	private final BoogieVarOrConst mBoogieVarOrConst;

	public EqBaseNode(BoogieVarOrConst bv) {
		mBoogieVarOrConst = bv;
	}
	
	public String toString() {
		return mBoogieVarOrConst.toString();
	}

	@Override
	public Term getTerm(Script s) {
		return mBoogieVarOrConst.getTerm();
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
