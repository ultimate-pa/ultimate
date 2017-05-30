package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

class OctagonSubstitutionTerm {
	private final TermVariable mVar;
	private final boolean mNegativeVar;
	private final Object mValue;

	protected OctagonSubstitutionTerm(Object value) {
		this(value, null, true);
	}

	protected OctagonSubstitutionTerm(Object value, TermVariable var, boolean negative) {
		mValue = value;
		mVar = var;
		mNegativeVar = negative;
	}

	public Object getValue() {
		return mValue;
	}

	boolean isZeroVar() {
		return mVar == null;
	}

	boolean isVarNegative() {
		return mNegativeVar;
	}

	TermVariable getVar() {
		return mVar;
	}

	@Override
	public String toString() {
		return (mVar == null) ? mValue.toString()
				: ((mNegativeVar ? ("-" + (mVar.toString())) : mVar.toString()) + ", " + mValue.toString());
	}
}
