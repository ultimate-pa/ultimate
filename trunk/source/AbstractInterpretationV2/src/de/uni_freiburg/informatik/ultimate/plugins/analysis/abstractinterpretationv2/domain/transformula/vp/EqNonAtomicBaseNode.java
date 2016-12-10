package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EqNonAtomicBaseNode extends EqNode {
	
	private final Term mTerm;

	EqNonAtomicBaseNode(Term t, boolean isGlobal) {
		super(isGlobal);
		mTerm = t;
	}

	@Override
	public Term getTerm(Script s) {
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
