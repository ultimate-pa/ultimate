package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqBaseNode extends EqNode {
	
	private final BoogieVarOrConst mBoogieVar;

	public EqBaseNode(BoogieVarOrConst bv) {
//		super(NonrelationalTermUtils.getTermVar(bv), bv.getDefaultConstant());
		mBoogieVar = bv;
	}
	
	public String toString() {
		return mBoogieVar.toString();
	}

	@Override
	public Term getTerm(Script s) {
//		if (mBoogieVar instanceof IProgramVar) {
//			return ((IProgramVar) mBoogieVar).getTermVariable();
//		} else {
//			return mBoogieVar.getDefaultConstant();
//		}
		return mBoogieVar.getTerm();
	}
	
	@Override
	public boolean equals(Object other) {
		if (!(other instanceof EqBaseNode)) {
			return false;
		}
		EqBaseNode ebn = (EqBaseNode) other;
		
		return ebn.mBoogieVar.equals(this.mBoogieVar);
	}
}
