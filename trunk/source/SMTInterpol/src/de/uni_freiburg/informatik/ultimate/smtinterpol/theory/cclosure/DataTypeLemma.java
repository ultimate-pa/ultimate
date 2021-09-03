package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

public class DataTypeLemma {

	private final RuleKind mRule;
	private final SymmetricPair<CCTerm>[] mReason;
	private final CCTerm[] mCycle;

	public DataTypeLemma(final RuleKind rule, final SymmetricPair<CCTerm>[] reason) {
		mRule = rule;
		mReason = reason;
		mCycle = null;
	}

	public DataTypeLemma(final RuleKind rule, final SymmetricPair<CCTerm>[] reason, final CCTerm[] cycle) {
		mRule = rule;
		mReason = reason;
		mCycle = cycle;
	}

	public RuleKind getRule() {
		return mRule;
	}

	public SymmetricPair<CCTerm>[] getReason() {
		return mReason;
	}

	public CCTerm[] getCycle() {
		return mCycle;
	}

	public Term[] getCycleTerms() {
		final Term[] cycleTerms = new Term[mCycle.length];
		int i = 0;
		for (final CCTerm ccTerm : mCycle) {
			cycleTerms[i++] = ccTerm.getFlatTerm();
		}
		return cycleTerms;
	}
}
