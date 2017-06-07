package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.math.BigDecimal;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Factory Class for creating OctagonConjunctions and OctagonTerms
 *
 * @author Jill Enke
 *
 */
public final class OctagonFactory {

	private OctagonFactory() {
	}

	/**
	 *
	 * @param value
	 * @param firstVar
	 * @param firstNegative
	 * @param secondVar
	 * @param secondNegative
	 * @return
	 */
	public static OctTerm createOctTerm(Object value, TermVariable firstVar, boolean firstNegative,
			TermVariable secondVar, boolean secondNegative) {
		if (firstVar.equals(secondVar)) {
			if (firstNegative != secondNegative) {
				throw new IllegalArgumentException("Can't create a term of the form x - x <= c");
			}
			return createOneVarOctTerm(value, firstVar, firstNegative);
		}
		return createTwoVarOctTerm(value, firstVar, firstNegative, secondVar, secondNegative);
	}

	public static OctTerm createOneVarOctTerm(Object value, TermVariable firstVar, boolean firstNegative) {
		if (value instanceof ParametricOctValue) {
			return new ParametricOctTerm((ParametricOctValue) value, firstVar, firstNegative);
		} else if (value instanceof BigDecimal) {
			return new StandardOctTerm((BigDecimal) value, firstVar, firstNegative);
		}
		return null;
	}

	public static OctTerm createTwoVarOctTerm(Object value, TermVariable firstVar, boolean firstNegative,
			TermVariable secondVar, boolean secondNegative) {
		if (value instanceof ParametricOctValue) {
			return new ParametricOctTerm((ParametricOctValue) value, firstVar, firstNegative, secondVar,
					secondNegative);
		} else if (value instanceof BigDecimal) {
			return new StandardOctTerm((BigDecimal) value, firstVar, firstNegative, secondVar, secondNegative);
		}
		return null;
	}

	public static OctConjunction createConjunction(Collection<OctTerm> terms) {
		final OctConjunction result = new OctConjunction();
		return result;

	}

}
