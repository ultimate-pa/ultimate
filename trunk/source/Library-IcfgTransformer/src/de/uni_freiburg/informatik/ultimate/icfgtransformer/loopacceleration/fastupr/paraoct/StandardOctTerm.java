package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.math.BigDecimal;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class StandardOctTerm extends OctTerm {

	public StandardOctTerm(BigDecimal constant, TermVariable firstVar, boolean firstNegative, TermVariable secondVar,
			boolean secondNegative) {
		super(constant, firstVar, firstNegative, secondVar, secondNegative);
	}

	public StandardOctTerm(BigDecimal constant, TermVariable firstVar, boolean firstNegative) {
		super(constant, firstVar, firstNegative);
	}

	@Override
	public BigDecimal getValue() {
		return (BigDecimal) mValue;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getLeftString());
		sb.append(" <= ");
		sb.append(getRightString());
		return sb.toString();
	}

	private String getLeftString() {
		if (isOneVar()) {
			return (mFirstNegative ? "-" : "") + "2*" + mFirstVar.toString();
		} else {
			return (mFirstNegative ? "-" : "") + mFirstVar.toString() + (mSecondNegative ? " -" : " +")
					+ mSecondVar.toString();
		}
	}

	private String getRightString() {
		return mValue.toString();
	}

	@Override
	protected Term rightTerm(Script script) {
		return script.decimal(getValue());
	}

	@Override
	protected String rightString() {
		return getValue().toString();
	}
}
