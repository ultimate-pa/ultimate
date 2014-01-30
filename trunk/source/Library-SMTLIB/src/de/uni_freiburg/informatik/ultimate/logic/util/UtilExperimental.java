package de.uni_freiburg.informatik.ultimate.logic.util;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

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
	
	/**
	 * Returns the equality ("=" lhs rhs), or true resp. false if some simple
	 * checks detect validity or unsatisfiablity of the equality.
	 */
	public static Term binaryEquality(Script script, Term lhs, Term rhs) {
		if (lhs == rhs) {
			return script.term("true");
		} else if (twoConstantTermsWithDifferentValue(lhs, rhs)) {
			return script.term("false");
		} else {
			return script.term("=", lhs, rhs);
		}
	}
	
	
	
	/**
	 * Returns true iff. fst and snd are different literals of the same numeric
	 * sort ("Int" or "Real").
	 * @exception Throws UnsupportedOperationException if both arguments do not
	 * have the same Sort.
	 */
	private static boolean twoConstantTermsWithDifferentValue(Term fst, Term snd) {
		if (!fst.getSort().equals(snd.getSort())) {
			throw new UnsupportedOperationException("arguments sort different");
		}
		if (!(fst instanceof ConstantTerm)) {
			return false;
		}
		if (!(snd instanceof ConstantTerm)) {
			return false;
		}
		if (!fst.getSort().isNumericSort()) {
			return false;
		}
		ConstantTerm fstConst = (ConstantTerm) fst;
		ConstantTerm sndConst = (ConstantTerm) snd;
		Object fstValue = fstConst.getValue();
		Object sndValue = sndConst.getValue();
		if (fstValue.getClass() != sndValue.getClass()) {
			return false;
		}
		return !fstConst.getValue().equals(sndConst.getValue());
		
	}
			
}
