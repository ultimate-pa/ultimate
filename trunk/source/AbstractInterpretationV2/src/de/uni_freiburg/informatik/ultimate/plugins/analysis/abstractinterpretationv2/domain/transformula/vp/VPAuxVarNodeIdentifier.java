package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class VPAuxVarNodeIdentifier extends VPNodeIdentifier {
	
	private final TermVariable mTv;
	
	public VPAuxVarNodeIdentifier(TermVariable tv) {
		super(null, null, null);
		mTv = tv;
	}
	
	public TermVariable getTermVariable() {
		return mTv;
	}

	@Override
	public boolean isFunction() {
		return false;
	}

	@Override
	public VPArrayIdentifier getFunction() {
		assert false;
		return null;
	}

	@Override
	public boolean isLiteral() {
		return false;
	}

}
