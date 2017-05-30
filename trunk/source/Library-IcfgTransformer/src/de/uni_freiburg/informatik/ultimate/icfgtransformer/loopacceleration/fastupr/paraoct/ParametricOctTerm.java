package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ParametricOctTerm extends OctTerm {

	public ParametricOctTerm(ParametricOctValue value, TermVariable firstVar, boolean firstNegative) {
		super(value, firstVar, firstNegative);
	}

	public ParametricOctTerm(ParametricOctValue value, TermVariable firstVar, boolean firstNegative,
			TermVariable secondVar, boolean secondNegative) {
		super(value, firstVar, firstNegative, secondVar, secondNegative);
	}

	@Override
	protected Term rightTerm(Script script) {
		return getValue().getTerm(script);
	}

	@Override
	public ParametricOctValue getValue() {
		return (ParametricOctValue) mValue;
	}

	@Override
	protected String rightString() {
		return getValue().toString();
	}

}
