/*
 * Copyright (C) 2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Class that provides static methods for the extraction of a satisfying
 * model from an SMT solver.
 * @author Jan Leike
 * @author Matthias Heizmann
 *
 */
public class ModelExtractionUtils {

	public static final long s_randomSeed = 80085;

	protected static final int s_numof_simultaneous_simplification_tests = 4;

	/**
	 * Convert a constant term retrieved from a model valuation to a Rational
	 *
	 * @param t
	 *            a term containing only +, -, *, / and numerals
	 * @return the rational represented by the term
	 * @throws TermException
	 *             if an error occurred while parsing the term
	 */
	public static Rational const2Rational(final Term t) throws TermException {
		if (t instanceof ApplicationTerm) {
			final ApplicationTerm appt = (ApplicationTerm) t;
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
			final Object o = ((ConstantTerm) t).getValue();
			if (o instanceof BigInteger) {
				return Rational.valueOf((BigInteger) o, BigInteger.ONE);
			} else if (o instanceof BigDecimal) {
				final BigDecimal decimal = (BigDecimal) o;
				Rational rat;
				if (decimal.scale() <= 0) {
					final BigInteger num = decimal.toBigInteger();
					rat = Rational.valueOf(num, BigInteger.ONE);
				} else {
					final BigInteger num = decimal.unscaledValue();
					final BigInteger denom = BigInteger.TEN.pow(decimal.scale());
					rat = Rational.valueOf(num, denom);
				}
				return rat;
			} else if (o instanceof Rational) {
				return (Rational) o;
			} else {
				throw new TermException(TermException.UNKNOWN_VALUE_CLASS, t);
			}
		}
		throw new TermException(TermException.UNKNOWN_TERM_STRUCTURE, t);
	}

	/**
	 * Extract a valuation from a script and convert ConstantTerms into
	 * Rationals
	 *
	 * @param script
	 * 			SMT script whose corresponding solver is in a state where
	 * 			checkSat() was called and the result was SAT.
	 * 			This method will not modify the assertion stack of the solver.
	 * @param coefficients
	 *            a collection of variables
	 * @return a valuation that assigns a Rational to every variable
	 * @throws TermException
	 *             if valuation generation or conversion fails
	 */
	public static Map<Term, Rational> getValuation(final Script script, final Collection<Term> coefficients)
			throws TermException {
		// assert mscript.checkSat() == LBool.SAT;
		final Map<Term, Rational> result = new LinkedHashMap<Term, Rational>();
		if (!coefficients.isEmpty()) {
			final Map<Term, Term> val = script.getValue(coefficients.toArray(new Term[coefficients.size()]));
			for (final Map.Entry<Term, Term> entry : val.entrySet()) {
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
	 * 			ILogger to which we write information about the simplification.
	 * @return the number of pops required on mscript
	 */
	@Deprecated
	protected int simplifyAssignment(final Script script, final ArrayList<Term> variables, final ILogger logger) {
		// Shuffle the variable list for better effect
		final Random rnd = new Random(s_randomSeed);
		Collections.shuffle(variables, rnd);

		int pops = 0;
		int checkSat_calls = 0;
		for (int i = 0; i < variables.size(); ++i) {
			final Term var = variables.get(i);
			script.push(1);
			script.assertTerm(script.term("=", var, SmtUtils.constructIntValue(script, BigInteger.ZERO)));
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
	 * 			ILogger to which we write information about the simplification.
	 * @param services
	 * @return an assignment with (hopefully) many zeros
	 * @throws TermException
	 *             if model extraction fails
	 */
	public static Map<Term, Rational> getSimplifiedAssignment(final Script script, final Collection<Term> variables,
			final ILogger logger, final IUltimateServiceProvider services) throws TermException {
		final Random rnd = new Random(s_randomSeed);
		Map<Term, Rational> val = getValuation(script, variables);

		final Set<Term> zero_vars = new HashSet<Term>(); // set of variables fixed to
													// 0
		final Set<Term> not_zero_vars = new HashSet<Term>(variables); // other
																// variables

		int checkSat_calls = 0;
		int unsat_calls = 0;
		while (true) {
			for (final Map.Entry<Term, Rational> entry : val.entrySet()) {
				if (entry.getValue().equals(Rational.ZERO)) {
					zero_vars.add(entry.getKey());
					not_zero_vars.remove(entry.getKey());
				}
			}
			if (not_zero_vars.size() <= s_numof_simultaneous_simplification_tests) {
				break;
			}
			if (!services.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(ModelExtractionUtils.class,
						"simplifying assignment for " + variables.size() + "variables");
			}
			script.push(1);
			for (final Term var : zero_vars) {
				script.assertTerm(script.term("=", var, Rational.ZERO.toTerm(var.getSort())));
			}
			for (int i = 0; i < 10; ++i) { // 10 is a good number
				final List<Term> vars = new ArrayList<Term>(not_zero_vars);
				// Shuffle the variable list for better effect
				Collections.shuffle(vars, rnd);

				final Term[] disj = new Term[s_numof_simultaneous_simplification_tests];
				for (int j = 0; j < s_numof_simultaneous_simplification_tests; ++j) {
					disj[j] = script.term("=", vars.get(j), Rational.ZERO.toTerm(vars.get(j).getSort()));
				}
				script.assertTerm(SmtUtils.or(script, disj));
			}
			++checkSat_calls;
			final LBool sat = script.checkSat();
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
		for (final Term var : zero_vars) {
			val.put(var, Rational.ZERO);
		}

		// Send stats to the logger
		logger.info("Simplification made " + checkSat_calls + " calls to the SMT solver.");
		int numzero_vars = 0;
		for (final Map.Entry<Term, Rational> entry : val.entrySet()) {
			if (entry.getValue().equals(Rational.ZERO)) {
				++numzero_vars;
			}
		}
		logger.info("Setting " + numzero_vars + " variables to zero.");

		return val;
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
	 * @param coefficients
	 *            the list of variables that can be set to 0
	 * @param logger
	 * 			ILogger to which we write information about the simplification.
	 * @param services
	 * @return an assignment with (hopefully) many zeros
	 * @throws TermException
	 *             if model extraction fails
	 */
	public static Map<Term, Rational> getSimplifiedAssignment_TwoMode(final Script script,
			final Collection<Term> coefficients, final ILogger logger, final IUltimateServiceProvider services)
			throws TermException {
		final Set<Term> alreadyZero = new HashSet<Term>(); // variables fixed to 0
		final Set<Term> zeroCandidates = new HashSet<Term>(coefficients); // variables that might be fixed to 0
		final Set<Term> neverZero = new HashSet<Term>(); // variables that will never become 0
		final Map<Term, Rational> finalValuation = new HashMap<Term, Rational>(getValuation(script, coefficients));

		{
			final List<Term> notYetAssertedZeros = findNewZeros(finalValuation, alreadyZero, zeroCandidates);
			for (final Term var : notYetAssertedZeros) {
				script.assertTerm(script.term("=", var, Rational.ZERO.toTerm(var.getSort())));
			}
		}
		final int variablesInitiallySetToZero = alreadyZero.size();

		boolean conjunctiveMode = false;
		double subsetSizeBonusFactor = 1.0;
		int pushWithoutPop = 0;
		int checkSatCalls = 0;
		Map<Term, Rational> newPartialValuation = null;
		while (!zeroCandidates.isEmpty()) {
			if (!services.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(ModelExtractionUtils.class,
						"simplifying assignment for " + coefficients.size() + "variables");
			}

			final int subsetSize = computeSubsetSize(zeroCandidates.size(), subsetSizeBonusFactor);
			final List<Term> subset = getSubset(subsetSize, zeroCandidates);
			final Term[] equalsZeroTerms = constructEqualsZeroTerms(script, subset);
			script.push(1);
			pushWithoutPop++;
			assert !subset.isEmpty() : "subset too small";
			if (subset.size() == 1) {
				assert equalsZeroTerms.length == 1;
				script.assertTerm(equalsZeroTerms[0]);
				final LBool sat = script.checkSat();
				checkSatCalls++;
				if (sat == LBool.SAT) {
					newPartialValuation = getValuation2(script, zeroCandidates, neverZero);
					finalValuation.putAll(newPartialValuation);
					for (final Term var : subset) {
						zeroCandidates.remove(var);
						alreadyZero.add(var);
					}
					conjunctiveMode = true;
					subsetSizeBonusFactor = 2.0;
				} else if (sat == LBool.UNSAT) {
					for (final Term var : subset) {
						zeroCandidates.remove(var);
						neverZero.add(var);
					}
					script.pop(1);
					pushWithoutPop--;
					newPartialValuation = null;
					conjunctiveMode = false;
					subsetSizeBonusFactor = 2.0;
				} else if (sat == LBool.UNKNOWN) {
					throw new AssertionError("not yet implemented");
				} else {
					throw new AssertionError("unknown LBool");
				}
			} else {
				// size > 1
				if (conjunctiveMode) {
					final Term conjunction = SmtUtils.and(script, equalsZeroTerms);
					script.assertTerm(conjunction);
					final LBool sat = script.checkSat();
					checkSatCalls++;
					if (sat == LBool.SAT) {
						newPartialValuation = getValuation2(script, zeroCandidates, neverZero);
						finalValuation.putAll(newPartialValuation);
						for (final Term var : subset) {
							zeroCandidates.remove(var);
							alreadyZero.add(var);
						}
						subsetSizeBonusFactor = 2.0;
					} else if (sat == LBool.UNSAT) {
						script.pop(1);
						pushWithoutPop--;
						newPartialValuation = null;
						conjunctiveMode = false;
					} else if (sat == LBool.UNKNOWN) {
						throw new AssertionError("not yet implemented");
					} else {
						throw new AssertionError("unknown LBool");
					}
				} else {
					// disjunctive mode
					final Term disjunction = SmtUtils.or(script, equalsZeroTerms);
					script.assertTerm(disjunction);
					final LBool sat = script.checkSat();
					checkSatCalls++;
					if (sat == LBool.SAT) {
						newPartialValuation = getValuation2(script, zeroCandidates, neverZero);
						finalValuation.putAll(newPartialValuation);
						script.pop(1);
						pushWithoutPop--;
						conjunctiveMode = true;
					} else if (sat == LBool.UNSAT) {
						for (final Term var : subset) {
							zeroCandidates.remove(var);
							neverZero.add(var);
						}
						script.pop(1);
						pushWithoutPop--;
						newPartialValuation = null;
						subsetSizeBonusFactor = 2.0;
					} else if (sat == LBool.UNKNOWN) {
						throw new AssertionError("not yet implemented");
					} else {
						throw new AssertionError("unknown LBool");
					}
				}
			}

			if (newPartialValuation != null) {
				final List<Term> notYetAssertedZeros = findNewZeros(finalValuation, alreadyZero, zeroCandidates);
				for (final Term var : notYetAssertedZeros) {
					script.assertTerm(script.term("=", var, Rational.ZERO.toTerm(var.getSort())));
				}
			}
		}
		//clear assertion stack
		for (int i=0; i<pushWithoutPop; i++) {
			script.push(1);
		}

		// Send stats to the logger
		logger.info("Simplification made " + checkSatCalls + " calls to the SMT solver.");
		logger.info(variablesInitiallySetToZero + " out of " + finalValuation.size()  +
				" variables were initially zero. Simplification set additionally " +
				(alreadyZero.size() - variablesInitiallySetToZero) + " variables to zero.");
		assert alreadyZero.size() + neverZero.size() == finalValuation.size() : "wrong number of variables";
		return finalValuation;
	}

	private static Map<Term, Rational> getValuation2(final Script script,
			final Set<Term> zeroCandidates, final Set<Term> neverZero) throws TermException {
		final List<Term> vars = new ArrayList<>(zeroCandidates.size() + neverZero.size());
		vars.addAll(zeroCandidates);
		vars.addAll(neverZero);
		return getValuation(script, vars);
	}

	private static int computeSubsetSize(final int zeroCandidates, final double subsetSizeBonusFactor) {
		return (int) Math.ceil(zeroCandidates * subsetSizeBonusFactor / 4.0);
	}

	/**
	 * Return subset with n elements. If n is greater then set.size() the
	 * return only set.size() elements.
	 */
	private static <E> List<E> getSubset(final int n, final Set<E> set) {
		final ArrayList<E> result = new ArrayList<E>();
		final int subsetSize = Math.min(n, set.size());
		final Iterator<E> it = set.iterator();
		for (int i=0; i<subsetSize; i++) {
			result.add(it.next());
		}
		return result;
	}


	/**
	 * Rreturn the equality (= t 0) for each t in set.
	 */
	private static Term[] constructEqualsZeroTerms(final Script script, final List<Term> set) {
		final Term[] result = new Term[set.size()];
		final Iterator<Term> it = set.iterator();
		for (int i=0; i<set.size(); i++) {
			final Term term = it.next();
			result[i] = script.term("=", term, Rational.ZERO.toTerm(term.getSort()));
		}
		return result;
	}

	/**
	 * Check for all zeroCandidates if they are mapped to Rational.ZERO in val.
	 * If yes, move the variable from the Set zeroCandidates to the set
	 * alreadyZero. Return all variables that were moved.
	 */
	private static List<Term> findNewZeros(final Map<Term, Rational> val,
			final Set<Term> alreadyZero, final Set<Term> zeroCandidates) {
		final List<Term> newlyBecomeZero = new ArrayList<Term>();
		final Iterator<Term> it = zeroCandidates.iterator();
		while (it.hasNext()) {
			final Term var = it.next();
			assert (val.containsKey(var));
			if (val.get(var).equals(Rational.ZERO)) {
				newlyBecomeZero.add(var);
				alreadyZero.add(var);
				it.remove();
			}
		}
		return newlyBecomeZero;
	}


}
