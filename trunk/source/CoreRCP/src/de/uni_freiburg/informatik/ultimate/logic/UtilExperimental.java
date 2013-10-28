package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * Class for all util methods that are not used in SmtInterpol.
 * (SmtInterpol uses the Util.java in this package)
 * @author Matthias Heizmann
 *
 */
public class UtilExperimental {
	
	/**
	 * TODO: This only works correct for integers (numerals). We need a 
	 * different version for rationals or add another parameter.  
	 */
	@Deprecated
	public static Term sum(Script script, Term... summands) {
		if (summands.length == 0) {
			return script.numeral(BigInteger.ZERO);
		} else if (summands.length == 1) {
			return summands[0];
		} else {
			return script.term("+", summands);
		}
	}
	
	/**
	 * Return term that represents the sum of all summands. Return the neutral
	 * element for sort sort if summands is empty.
	 */
	public static Term sum(Script script, Sort sort, Term... summands) {
		assert sort.isNumericSort();
		if (summands.length == 0) {
			if (sort.toString().equals("Int")) {
				return script.numeral(BigInteger.ZERO);
			} else if (sort.toString().equals("Real")) {
				return script.decimal(BigDecimal.ZERO);
			} else {
				throw new UnsupportedOperationException("unkown sort " + sort);
			}
		} else if (summands.length == 1) {
			return summands[0];
		} else {
			return script.term("+", summands);
		}
	}
	
	
	public static Term binaryEquality(Script script, Term lhs, Term rhs) {
		if (lhs == rhs) {
			return script.term("true");
		} else if (isIntLiteral(rhs) && isIntLiteral(lhs)) {
			return script.term("false");
		} else {
			return script.term("=", lhs, rhs);
		}
	}
	
	private static boolean isIntLiteral(Term term) {
		if (term instanceof ConstantTerm) {
			return term.getSort().getName().equals("Int"); 
		} else {
			return false;
		}
	}
			
}
