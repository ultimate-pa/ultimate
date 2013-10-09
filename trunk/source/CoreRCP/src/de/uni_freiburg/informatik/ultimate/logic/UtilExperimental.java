package de.uni_freiburg.informatik.ultimate.logic;

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
	public static Term sum(Script script, Term... summands) {
		if (summands.length == 0) {
			return script.numeral(BigInteger.ZERO);
		} else if (summands.length == 1) {
			return summands[0];
		} else {
			return script.term("+", summands);
		}
	}
}
