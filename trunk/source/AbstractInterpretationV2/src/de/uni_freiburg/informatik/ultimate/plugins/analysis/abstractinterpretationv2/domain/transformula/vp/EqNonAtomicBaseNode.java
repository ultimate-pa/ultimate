package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class EqNonAtomicBaseNode extends EqNode {
	
	EqNonAtomicBaseNode(Term t, boolean isGlobal) {
		super(isGlobal, t.getFreeVars().length == 0);
		mTerm = t;
	}

	@Override
	public boolean isLiteral() {
		return false;
	}

	@Override
	public String toString() {
		return mTerm.toString();
	}
	
	
	@Override
	public boolean isFunction() {
		return false;
	}

	@Override
	public IProgramVarOrConst getFunction() {
		assert false : "check for isFunction() first";
		return null;
	}
}
