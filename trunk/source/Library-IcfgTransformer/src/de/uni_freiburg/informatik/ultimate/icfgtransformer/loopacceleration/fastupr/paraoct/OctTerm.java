package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public abstract class OctTerm {

	protected final TermVariable mFirstVar;
	protected final TermVariable mSecondVar;
	protected final boolean mFirstNegative;
	protected final boolean mSecondNegative;
	protected final Object mValue;

	public OctTerm(Object value, TermVariable firstVar, boolean firstNegative, TermVariable secondVar,
			boolean secondNegative) {
		mValue = value;
		mFirstVar = firstVar;
		mFirstNegative = firstNegative;
		mSecondVar = secondVar;
		mSecondNegative = secondNegative;
	}

	public OctTerm(Object value, TermVariable firstVar, boolean firstNegative) {
		mValue = value;
		mFirstVar = firstVar;
		mFirstNegative = firstNegative;
		mSecondVar = firstVar;
		mSecondNegative = firstNegative;
	}

	/**
	 * Converts the OctTerm to a Term
	 *
	 * @param script
	 *            Script to build Terms
	 * @return Fresh Term representing the OctTerm
	 */
	public Term toTerm(Script script) {
		final Term leftTerm = leftTerm(script);
		final Term rightTerm = rightTerm(script);
		return script.term("<=", leftTerm, rightTerm);
	}

	protected Term leftTerm(Script script) {
		if (isOneVar()) {
			return script.term("*",
					isFirstNegative() ? script.numeral((new BigInteger("2")).negate()) : script.numeral("2"),
					mFirstVar);

		} else {
			return script.term("+",
					isFirstNegative() ? script.term("*", script.numeral(BigInteger.ONE.negate()), mFirstVar)
							: mFirstVar,
					isSecondNegative() ? script.term("*", script.numeral(BigInteger.ONE.negate()), mSecondVar)
							: mSecondVar);
		}
	}

	protected abstract Term rightTerm(Script script);

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (isOneVar()) {
			sb.append((isFirstNegative() ? "-" : "") + "2*" + mFirstVar.toString());
		} else {
			sb.append((isFirstNegative() ? "-" : "") + mFirstVar.toString() + " + " + (isSecondNegative() ? "-" : "")
					+ mSecondVar.toString());
		}
		sb.append(" <= ");
		sb.append(rightString());
		return sb.toString();
	}

	protected abstract String rightString();

	public abstract Object getValue();

	public boolean isOneVar() {
		return mFirstNegative == mSecondNegative && mFirstVar == mSecondVar;
	}

	public TermVariable getFirstVar() {
		return mFirstVar;
	}

	public TermVariable getSecondVar() {
		return mSecondVar;
	}

	public boolean isFirstNegative() {
		return mFirstNegative;
	}

	public boolean isSecondNegative() {
		return mSecondNegative;
	}
}
