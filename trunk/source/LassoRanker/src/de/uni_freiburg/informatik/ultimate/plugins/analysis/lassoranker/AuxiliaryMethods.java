package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;

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
		try {
			script.declareFun(name, new Sort[0], script.sort("Real"));
		} catch(SMTLIBException iae) {
			if (!iae.getMessage().endsWith("already defined.")) {
				throw iae;
			} else {
				// The function is already defined
				// --> Silence the exception
			}
		}
		return script.term(name);
	}
	
	/**
	 * Convert a Rational into a decimal instance.
	 */
	public static Term rationalToDecimal(Script script, Rational a) {
		Term num = script.decimal(a.numerator().abs().toString());
		Term denom = script.decimal(a.denominator().abs().toString());
		boolean negative = a.numerator().signum() * a.denominator().signum()
				== -1;
		Term t = script.term("/", num, denom);
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
	public static Rational decimalToRational(BigDecimal d) {
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
	public static Rational convertCT(ConstantTerm ct)
			throws TermException {
		if (ct.getSort().getName().equals("Rational")) {
			return (Rational) ct.getValue();
		} else if (ct.getSort().getName().equals("Real")) {
			BigDecimal d = (BigDecimal) ct.getValue();
			return (Rational) AuxiliaryMethods.decimalToRational(d);
		} else if (ct.getSort().getName().equals("Int")) {
			Rational r = Rational.valueOf((BigInteger) ct.getValue(),
					BigInteger.ONE);
			return r;
		} else
			throw new TermException(
					"Trying to convert a ConstantTerm of unknown sort.", ct);
	}
	
	/**
	 * Convert a constant term retrieved from a model valuation to a Rational
	 * @param t a term containing only +, -, *, / and numerals
	 * @return the rational represented by the term
	 */
	public static Rational const2Rational(Term t) {
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
				assert(false); // Unknown value class
			}
		}
		assert(false); // Unknown term structure
		return null;
	}
	
	/**
	 * Convert a predicate logical formula into disjunctive normal form
	 * @param formula a predicate logic formula
	 * @return collection of clauses equivalent to the input formula
	 */
	public static Collection<Term> toDNF(Script script, Term formula) {
		Collection<Term> clauses = new HashSet<Term>();
		if (!(formula instanceof ApplicationTerm)) {
			clauses.add(formula);
		} else {
			ApplicationTerm appt = (ApplicationTerm) formula;
			if (appt.getFunction().getName() == "and") {
				List<Iterator<Term>> it_list = new ArrayList<Iterator<Term>>();
				List<Collection<Term>> dnfs = new ArrayList<Collection<Term>>();
				List<Term> current = new ArrayList<Term>();
				// Convert every parameter to DNF
				for (Term param : appt.getParameters()) {
					Collection<Term> dnf = toDNF(script, param);
					if (dnf.isEmpty()) {
						return clauses;
					}
					dnfs.add(dnf);
					Iterator<Term> it = dnf.iterator();
					current.add(it.next());
					it_list.add(it);
				}
				while (true) {
					clauses.add(script.term("and",
							current.toArray(new Term[0])));
					
					// Advance the iterators
					int i = 0;
					while (i < it_list.size() && !it_list.get(i).hasNext()) {
						// Reset the iterator
						Iterator<Term> it = dnfs.get(i).iterator();
						current.set(i, it.next());
						it_list.set(i, it);
						++i;
					}
					if (i >= it_list.size()) {
						break; // All permutations have been considered
					}
					Term t = it_list.get(i).next();
					current.set(i, t);
				}
			} else if (appt.getFunction().getName() == "or") {
				for (Term param : appt.getParameters()) {
					clauses.addAll(toDNF(script, param));
				}
			} else if (appt.getFunction().getName() == "not") {
				assert (appt.getParameters().length == 1);
				Term notTerm = appt.getParameters()[0];
				if ((notTerm instanceof TermVariable)) {
					clauses.add(notTerm);
				} else {
					clauses.add(negateAtom(script, notTerm));
					// TODO: case where notTerm is not an atom
				}
			} else if (appt.getFunction().getName() == "=>") {
				clauses.addAll(toDNF(script, script.term("not", appt.getParameters()[0])));
				clauses.addAll(toDNF(script, appt.getParameters()[1]));
			} else if (appt.getFunction().getName() == "=" &&
					appt.getParameters()[0].getSort().getName().equals("Bool")) {
				Term param1 = appt.getParameters()[0];
				Term param2 = appt.getParameters()[1];
				clauses.addAll(toDNF(script, script.term("and",
						script.term("=>", param1, param2),
						script.term("=>", param2, param1))));
			} else {
				clauses.add(appt);
			}
		}
		return clauses;
	}
	
	private static Term negateAtom(Script script, Term term) {
		assert (term instanceof ApplicationTerm);
		ApplicationTerm appNotTerm = (ApplicationTerm) term;
		Term[] params = appNotTerm.getParameters();
		if (appNotTerm.getFunction().getName() == "<=") {
			assert (params.length == 2) : "chaining not supported";
			return script.term(">", params);
		} else if (appNotTerm.getFunction().getName() == ">=") {
			assert (params.length == 2) : "chaining not supported";
			return script.term("<", params);
		} else if (appNotTerm.getFunction().getName() == "<") {
			assert (params.length == 2) : "chaining not supported";
			return script.term(">=", params);
		} else if (appNotTerm.getFunction().getName() == ">") {
			assert (params.length == 2) : "chaining not supported";
			return script.term("<=", params);
		} else {
			throw new UnsupportedOperationException("Not yet implemented");
		}
	}
}
