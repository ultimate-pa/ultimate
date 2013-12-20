package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;


/**
 * Random collection of various methods that don't fit in anywhere else
 * 
 * @author Jan Leike
 */
public class AuxiliaryMethods {
	/**
	 * Define a new constant of sort "Real".
	 * @param script SMT Solver
	 * @param name name of the new constant
	 * @return the new variable as a term
	 * @throws SMTLIBException if something goes wrong, e.g. the name is
	 *          already defined
	 */
	public static Term newRealConstant(Script script, String name)
			throws SMTLIBException {
		script.declareFun(name, new Sort[0], script.sort("Real"));
		return script.term(name);
	}
	
	/**
	 * Convert a Rational into a decimal instance.
	 */
	static Term rationalToDecimal(Script script, Rational a) {
		Term num = script.decimal(a.numerator().abs().toString());
		Term denom = script.decimal(a.denominator().abs().toString());
		boolean negative = a.numerator().signum() * a.denominator().signum()
				== -1;
		Term  t = num;
		if (!a.isIntegral()) {
			t = script.term("/", num, denom);
		}
		if (negative) {
			t = script.term("-", t);
		}
		return t;
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
			if (appt.getFunction().getName() == "+") {
				return const2Rational(appt.getParameters()[0]).add(
						const2Rational(appt.getParameters()[1]));
			}
			if (appt.getFunction().getName() == "-") {
				if (appt.getParameters().length == 1) {
					return const2Rational(appt.getParameters()[0]).mul(
							Rational.MONE);
				} else {
					return const2Rational(appt.getParameters()[0]).sub(
							const2Rational(appt.getParameters()[1]));
				}
			}
			if (appt.getFunction().getName() == "*") {
				return const2Rational(appt.getParameters()[0]).mul(
						const2Rational(appt.getParameters()[1]));
			}
			if (appt.getFunction().getName() == "/") {
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
		throw new TermException("Unkown term structure", t);
	}
	
	static Map<Term, Rational> preprocessValuation(Map<Term, Term> val)
			throws TermException {
		Map<Term, Rational> new_val = new HashMap<Term, Rational>();
		for (Entry<Term, Term> entry : val.entrySet()) {
			new_val.put(entry.getKey(),
					AuxiliaryMethods.const2Rational(entry.getValue()));
		}
		return new_val;
	}
	
	/**
	 * Create a new TransForumla that has an inVar for all outVars.
	 * 
	 * This is required to prevent a problem that was reported by Matthias
	 * in Madrid.bpl. This problem occurs when there are outVars that do not
	 * have a corresponding inVar. Supporting invariant generation then becomes
	 * unsound for the inductiveness property.
	 * 
	 * @param formula input
	 * @return copy of the input formula with more inVars
	 */
	static TransFormula matchInVars(Boogie2SMT boogie2smt, TransFormula formula) {
		Map<BoogieVar, TermVariable> inVars =
				new HashMap<BoogieVar, TermVariable>(formula.getInVars());
		for (Entry<BoogieVar, TermVariable> entry : formula.getOutVars().entrySet()) {
			if (!inVars.containsKey(entry.getKey())) {
				TermVariable inVar = TransFormula.getFreshVariable(boogie2smt,
						entry.getKey(), entry.getValue().getSort());
				inVars.put(entry.getKey(), inVar);
			}
		}
		return new TransFormula(
				formula.getFormula(),
				inVars,
				new HashMap<BoogieVar, TermVariable>(formula.getOutVars()),
				new HashSet<TermVariable>(formula.getAuxVars()),
				new HashSet<TermVariable>(formula.getBranchEncoders()),
				formula.isInfeasible(),
				formula.getClosedFormula()
		);
	}
}
