package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.math.BigDecimal;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Parametric Octagon Values A parametric octagon has values of the form: a*k + b, where a, b are constant, k is an
 * OutVar
 */

public class ParametricOctValue {

	private final BigDecimal mA;
	private final BigDecimal mB;
	private final TermVariable mK;

	ParametricOctValue() {
		mA = new BigDecimal("0");
		mB = new BigDecimal("0");
		mK = null;
	}
}
