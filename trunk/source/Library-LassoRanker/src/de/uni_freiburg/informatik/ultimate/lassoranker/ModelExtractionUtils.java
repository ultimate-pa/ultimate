package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * Class that provides static methods for the extraction of a satisfying 
 * model from an SMT solver.
 * @author Jan Leike, Matthias Heizmann
 *
 */
public class ModelExtractionUtils {
	
	public static final long s_randomSeed = 80085;

	protected static final int s_num_of_simultaneous_simplification_tests = 4;
	
	/**
	 * Convert a constant term retrieved from a model valuation to a Rational
	 * 
	 * @param t
	 *            a term containing only +, -, *, / and numerals
	 * @return the rational represented by the term
	 * @throws TermException
	 *             if an error occurred while parsing the term
	 */
	public static Rational const2Rational(Term t) throws TermException {
		if (t instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) t;
			if (appt.getFunction().getName().equals("+")) {
				return const2Rational(appt.getParameters()[0]).add(const2Rational(appt.getParameters()[1]));
			}
			if (appt.getFunction().getName().equals("-")) {
				if (appt.getParameters().length == 1) {
					return const2Rational(appt.getParameters()[0]).mul(Rational.MONE);
				} else {
					return const2Rational(appt.getParameters()[0]).sub(const2Rational(appt.getParameters()[1]));
				}
			}
			if (appt.getFunction().getName().equals("*")) {
				return const2Rational(appt.getParameters()[0]).mul(const2Rational(appt.getParameters()[1]));
			}
			if (appt.getFunction().getName().equals("/")) {
				return const2Rational(appt.getParameters()[0]).div(const2Rational(appt.getParameters()[1]));
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

	/**
	 * Extract a valuation from a script and convert ConstantTerms into
	 * Rationals
	 * 
	 * @param script
	 * 			SMT script whose corresponding solver is in a state where
	 * 			checkSat() was called and the result was SAT.
	 * 			This method will not modify the assertion stack of the solver.
	 * @param vars
	 *            a collection of variables
	 * @return a valuation that assigns a Rational to every variable
	 * @throws TermException
	 *             if valuation generation or conversion fails
	 */
	public static Map<Term, Rational> getValuation(Script script, Collection<Term> vars) throws TermException {
		// assert m_script.checkSat() == LBool.SAT;
		Map<Term, Rational> result = new LinkedHashMap<Term, Rational>();
		if (!vars.isEmpty()) {
			Map<Term, Term> val = script.getValue(vars.toArray(new Term[vars.size()]));
			for (Map.Entry<Term, Term> entry : val.entrySet()) {
				result.put(entry.getKey(), const2Rational(entry.getValue()));
			}
		}
		return result;
	}
	
	
	/**
	 * Tries to simplify a satisfying assignment by assigning zeros to
	 * variables. Gets stuck in local optima.
	 * 
	 * The procedure works according to this principle:
	 * 
	 * <pre>
	 * random.shuffle(variables)
	 * for v in variables:
	 *     if sat with v = 0:
	 *         set v to 0
	 * </pre>
	 * @param script
	 * 			SMT script whose corresponding solver is in a state where
	 * 			checkSat() was called and the result was SAT.
	 * 			This method will not modify the assertion stack of the solver.
	 * @param variables
	 *            the list of variables that can be set to 0
	 * @param logger
	 * 			Logger to which we write information about the simplification.
	 * @return the number of pops required on m_script
	 */
	@Deprecated
	protected int simplifyAssignment(Script script, ArrayList<Term> variables, Logger logger) {
		// Shuffle the variable list for better effect
		Random rnd = new Random(s_randomSeed);
		Collections.shuffle(variables, rnd);

		int pops = 0;
		int checkSat_calls = 0;
		for (int i = 0; i < variables.size(); ++i) {
			Term var = variables.get(i);
			script.push(1);
			script.assertTerm(script.term("=", var, script.numeral(BigInteger.ZERO)));
			LBool sat = script.checkSat();
			++checkSat_calls;
			if (sat != LBool.SAT) {
				script.pop(1);
				// Make sure we call checkSat() after the last pop()
				if (i == variables.size() - 1) {
					sat = script.checkSat();
					++checkSat_calls;
					assert sat == LBool.SAT;
				}
			} else {
				pops += 1;
			}
		}
		logger.info("Simplification made " + checkSat_calls + " calls to the SMT solver.");
		return pops;
	}
	
	/**
	 * Tries to simplify a satisfying assignment by assigning zeros to
	 * variables. Gets stuck in local optima.
	 * 
	 * This is a more efficient version
	 * @param script
	 * 			SMT script whose corresponding solver is in a state where
	 * 			checkSat() was called and the result was SAT.
	 * 			This method will not modify the assertion stack of the solver.
	 * @param variables
	 *            the list of variables that can be set to 0
	 * @param logger
	 * 			Logger to which we write information about the simplification.
	 * @return an assignment with (hopefully) many zeros
	 * @throws TermException
	 *             if model extraction fails
	 */
	public static Map<Term, Rational> getSimplifiedAssignment(Script script, 
			Collection<Term> variables, Logger logger) throws TermException {
		Random rnd = new Random(s_randomSeed);
		Term zero = script.numeral("0");
		Map<Term, Rational> val = getValuation(script, variables);

		Set<Term> zero_vars = new HashSet<Term>(); // set of variables fixed to
													// 0
		Set<Term> not_zero_vars = new HashSet<Term>(variables); // other
																// variables

		int checkSat_calls = 0;
		int unsat_calls = 0;
		while (true) {
			for (Map.Entry<Term, Rational> entry : val.entrySet()) {
				if (entry.getValue().equals(Rational.ZERO)) {
					zero_vars.add(entry.getKey());
					not_zero_vars.remove(entry.getKey());
				}
			}
			if (not_zero_vars.size() <= s_num_of_simultaneous_simplification_tests) {
				break;
			}
			script.push(1);
			for (Term var : zero_vars) {
				script.assertTerm(script.term("=", var, zero));
			}
			for (int i = 0; i < 10; ++i) { // 10 is a good number
				List<Term> vars = new ArrayList<Term>(not_zero_vars);
				// Shuffle the variable list for better effect
				Collections.shuffle(vars, rnd);

				Term[] disj = new Term[s_num_of_simultaneous_simplification_tests];
				for (int j = 0; j < s_num_of_simultaneous_simplification_tests; ++j) {
					disj[j] = script.term("=", vars.get(j), zero);
				}
				script.assertTerm(Util.or(script, disj));
			}
			++checkSat_calls;
			LBool sat = script.checkSat();
			if (sat == LBool.SAT) {
				val = getValuation(script, not_zero_vars);
			} else {
				++unsat_calls;
				if (unsat_calls > 1) {
					// too many unsuccessful calls, so give up
					script.pop(1);
					break;
				}
			}
			script.pop(1);
		}

		// Add zero variables to the valuation
		for (Term var : zero_vars) {
			val.put(var, Rational.ZERO);
		}

		// Send stats to the logger
		logger.info("Simplification made " + checkSat_calls + " calls to the SMT solver.");
		int num_zero_vars = 0;
		for (Map.Entry<Term, Rational> entry : val.entrySet()) {
			if (entry.getValue().equals(Rational.ZERO)) {
				++num_zero_vars;
			}
		}
		logger.info("Setting " + num_zero_vars + " variables to zero.");

		return val;
	}
	


}
