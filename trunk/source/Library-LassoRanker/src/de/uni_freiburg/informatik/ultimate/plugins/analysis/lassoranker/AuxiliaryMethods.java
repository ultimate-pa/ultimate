/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;


/**
 * Random collection of various methods that don't fit in anywhere else
 * 
 * @author Jan Leike
 */
public class AuxiliaryMethods {
	/**
	 * Define a new constant
	 * @param script SMT Solver
	 * @param name name of the new constant
	 * @param sort the sort of the variable
	 * @return the new variable as a term
	 * @throws SMTLIBException if something goes wrong, e.g. the name is
	 *          already defined
	 */
	public static Term newConstant(Script script, String name, String sortname)
			throws SMTLIBException {
		script.declareFun(name, new Sort[0], script.sort(sortname));
		return script.term(name);
	}
	
	/**
	 * Convert a BigDecimal into a Rational.
	 * Stolen from Jochen's code
	 * de.uni_freiburg.informatik.ultimate.smtinterpol.convert.ConvertFormula.
	 */
	static Rational decimalToRational(BigDecimal d) {
		Rational rat;
		if (d.scale() <= 0) {
			BigInteger num = d.toBigInteger();
			rat = Rational.valueOf(num, BigInteger.ONE);
		} else {
			BigInteger num = d.unscaledValue();
			BigInteger denom = BigInteger.TEN.pow(d.scale());
			rat = Rational.valueOf(num, denom);
		}
		return rat;
	}
	
	/**
	 * Convert a constant term to Rational
	 * Extracts the value of the number from the term
	 * @param ct constant term
	 * @return rational from the value of ct
	 */
	static Rational convertCT(ConstantTerm ct)
			throws TermException {
		if (ct.getSort().getName().equals("Rational")) {
			return (Rational) ct.getValue();
		} else if (ct.getSort().getName().equals("Real")) {
			BigDecimal d = (BigDecimal) ct.getValue();
			return (Rational) AuxiliaryMethods.decimalToRational(d);
		} else if (ct.getSort().getName().equals("Int")) {
			if (ct.getValue() instanceof Rational) {
				return (Rational) ct.getValue();
			} else {
				Rational r = Rational.valueOf((BigInteger) ct.getValue(),
					BigInteger.ONE);
				return r;
			}
		} else
			throw new TermException(
					"Trying to convert a ConstantTerm of unknown sort.", ct);
	}
	
	/**
	 * Convert a constant term retrieved from a model valuation to a Rational
	 * @param t a term containing only +, -, *, / and numerals
	 * @return the rational represented by the term
	 * @throws TermException if an error occurred while parsing the term
	 */
	static Rational const2Rational(Term t) throws TermException {
		if (t instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) t;
			if (appt.getFunction().getName().equals("+")) {
				return const2Rational(appt.getParameters()[0]).add(
						const2Rational(appt.getParameters()[1]));
			}
			if (appt.getFunction().getName().equals("-")) {
				if (appt.getParameters().length == 1) {
					return const2Rational(appt.getParameters()[0]).mul(
							Rational.MONE);
				} else {
					return const2Rational(appt.getParameters()[0]).sub(
							const2Rational(appt.getParameters()[1]));
				}
			}
			if (appt.getFunction().getName().equals("*")) {
				return const2Rational(appt.getParameters()[0]).mul(
						const2Rational(appt.getParameters()[1]));
			}
			if (appt.getFunction().getName().equals("/")) {
				return const2Rational(appt.getParameters()[0]).div(
						const2Rational(appt.getParameters()[1]));
			}
		}
		if (t instanceof ConstantTerm) {
			Object o = ((ConstantTerm) t).getValue();
			if (o instanceof BigInteger) {
				return Rational.valueOf((BigInteger) o, BigInteger.ONE);
			} else if (o instanceof BigDecimal) {
				BigDecimal decimal = (BigDecimal) o;
				Rational rat;
				if (decimal.scale() <= 0) {
					BigInteger num = decimal.toBigInteger();
					rat = Rational.valueOf(num, BigInteger.ONE);
				} else {
					BigInteger num = decimal.unscaledValue();
					BigInteger denom = BigInteger.TEN.pow(decimal.scale());
					rat = Rational.valueOf(num, denom);
				}
				return rat;
			} else if (o instanceof Rational) {
				return (Rational) o;
			} else {
				throw new TermException("Unknown value class", t);
			}
		}
		throw new TermException("Unknown term structure", t);
	}
	
	static Map<Term, Rational> preprocessValuation(Map<Term, Term> val)
			throws TermException {
		Map<Term, Rational> new_val = new HashMap<Term, Rational>();
		for (Map.Entry<Term, Term> entry : val.entrySet()) {
			new_val.put(entry.getKey(), const2Rational(entry.getValue()));
		}
		return new_val;
	}
}
