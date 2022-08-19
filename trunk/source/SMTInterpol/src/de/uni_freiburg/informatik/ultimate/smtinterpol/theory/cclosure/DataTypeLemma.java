package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

public class DataTypeLemma {

	private final RuleKind mRule;
	private final SymmetricPair<CCTerm> mMainEquality;
	private final SymmetricPair<CCTerm>[] mReason;
	private final Object[] mAnnotation;

	/**
	 * Constructor for the rule dt-constructor
	 *
	 * @param rule         must be DT_CONSTRUCTOR
	 * @param mainEquality the propagated equality {@code u = C(s1(u),...,sn(u))}.
	 * @param reason       the equality isC(u) = true.
	 */
	public DataTypeLemma(final RuleKind rule, final SymmetricPair<CCTerm> mainEquality,
			final SymmetricPair<CCTerm>[] reason) {
		mRule = rule;
		mReason = reason;
		mMainEquality = mainEquality;
		mAnnotation = null;
	}

	/**
	 * Constructor for the rule dt-project or dt-tester.
	 *
	 * @param rule         must be DT_PROJECT or DT_TESTER
	 * @param mainEquality the propagated equality {@code s(u) = ai} or
	 *                     {@code isC(u) = false/true}.
	 * @param reason       the equalities to prove u = consTerm
	 * @param consTerm1    the constructor {@code C(a1,...,an)} to which u is equal.
	 */
	public DataTypeLemma(final RuleKind rule, final SymmetricPair<CCTerm> mainEquality,
			final SymmetricPair<CCTerm>[] reason, final CCTerm consTerm) {
		assert rule == RuleKind.DT_PROJECT || rule == RuleKind.DT_TESTER;
		mRule = rule;
		mReason = reason;
		mMainEquality = mainEquality;
		mAnnotation = new Object[] { ":cons", consTerm.getFlatTerm() };
	}

	/**
	 * Constructor for the rule dt-injective.
	 *
	 * @param rule         must be DT_INJECTIVE
	 * @param mainEquality the propagated equality {@code ai=bi}
	 * @param reason       the equalities to prove consTerm1 = consTerm2
	 * @param consTerm1    the first constructor {@code C(a1,...,an)}
	 * @param consTerm2    the second constructor {@code C(b1,...,bn)}
	 */
	public DataTypeLemma(final RuleKind rule, final SymmetricPair<CCTerm> mainEquality,
			final SymmetricPair<CCTerm>[] reason, final CCTerm consTerm1, final CCTerm consTerm2) {
		assert rule == RuleKind.DT_INJECTIVE;
		mRule = rule;
		mReason = reason;
		mMainEquality = mainEquality;
		mAnnotation = new Object[] { ":cons", consTerm1.getFlatTerm(), consTerm2.getFlatTerm() };
	}

	/**
	 * Constructor for the rule dt-disjoint.
	 *
	 * @param rule      must be DT_DISJOINT
	 * @param reason    the equalities to prove consTerm1 = consTerm2
	 * @param consTerm1 the first constructor {@code C1(...)}
	 * @param consTerm2 the second constructor {@code C2(...)}
	 */
	public DataTypeLemma(final RuleKind rule, final SymmetricPair<CCTerm>[] reason, final CCTerm consTerm1,
			final CCTerm consTerm2) {
		assert rule == RuleKind.DT_DISJOINT;
		mRule = rule;
		mReason = reason;
		mMainEquality = null;
		mAnnotation = new Object[] { ":cons", consTerm1.getFlatTerm(), consTerm2.getFlatTerm() };
	}

	public DataTypeLemma(final RuleKind rule,
			final SymmetricPair<CCTerm>[] reason, final Term[] testerTerms) {
		assert rule == RuleKind.DT_CASES || rule == RuleKind.DT_UNIQUE;
		mRule = rule;
		mReason = reason;
		mMainEquality = null;
		mAnnotation = testerTerms;
	}

	public DataTypeLemma(final RuleKind rule, final SymmetricPair<CCTerm>[] reason, final CCTerm[] cycle) {
		assert rule == RuleKind.DT_CYCLE;
		mRule = rule;
		mReason = reason;
		mMainEquality = null;
		mAnnotation = new Object[] { ":cycle", getCycleTerms(cycle) };
	}

	public RuleKind getRule() {
		return mRule;
	}

	public SymmetricPair<CCTerm> getMainEquality() {
		return mMainEquality;
	}

	public SymmetricPair<CCTerm>[] getReason() {
		return mReason;
	}

	public Object[] getAnnotation() {
		return mAnnotation == null ? new Object[0] : mAnnotation;
	}

	private Term[] getCycleTerms(final CCTerm[] cycle) {
		final Term[] cycleTerms = new Term[cycle.length];
		int i = 0;
		for (final CCTerm ccTerm : cycle) {
			cycleTerms[i++] = ccTerm.getFlatTerm();
		}
		return cycleTerms;
	}

	@Override
	public String toString() {
		return "DataTypeLemma[" + mRule + "," + mMainEquality + "," + Arrays.toString(mAnnotation) + "]";
	}
}
