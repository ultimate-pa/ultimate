package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.*;


/**
 * Produces more human-readable String instances for SMT Terms
 * 
 * Warning: this probably implements only a small subset of the SMT terms,
 * use at your own risk!
 * 
 * @author Jan Leike
 */
public class SMTTermPrinter {
	
	public static String print(Term t) {
		// t is a constant term
		if (t instanceof ConstantTerm) {
			ConstantTerm ct = (ConstantTerm) t;
			if (ct.getValue() instanceof Rational) {
				Rational r = (Rational) ct.getValue();
				if (r.denominator().equals(BigInteger.ONE)) {
					return r.denominator().toString();
				}
				return r.toString();
			}
			return ct.toString();
		}
		if (!(t instanceof ApplicationTerm)) {
			return t.toString();
		}
		ApplicationTerm appt = (ApplicationTerm) t;
		if (appt.getParameters().length == 2) {
			// Write the operator infix
			return print(appt.getParameters()[0])
					+ " " + appt.getFunction().getName() + " "
					+ print(appt.getParameters()[1]);
		}
		return t.toStringDirect();
	}
}
