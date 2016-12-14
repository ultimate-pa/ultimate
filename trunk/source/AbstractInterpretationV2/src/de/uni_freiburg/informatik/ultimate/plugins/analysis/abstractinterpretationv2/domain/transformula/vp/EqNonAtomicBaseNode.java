package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class EqNonAtomicBaseNode extends EqNode {
	
	private final Term mTerm;

	EqNonAtomicBaseNode(Term t, boolean isGlobal) {
		super(isGlobal, t.getFreeVars().length == 0);
		mTerm = t;
	}

	@Override
	public Term getTerm(ManagedScript s) {
		return mTerm;
	}

	@Override
	public boolean isLiteral() {
		return false;
	}

	@Override
	public String toString() {
		return mTerm.toString();
	}
}
