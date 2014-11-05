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
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.Closeable;
import java.io.IOException;
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

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Superclass to TerminationArgumentSynthesizer and
 * NonTerminationArgumentSynthesizer.
 * 
 * Contains some shared code.
 * 
 * @author Jan Leike
 * @see TerminationArgumentSynthesizer
 * @see NonTerminationArgumentSynthesizer
 */
public abstract class ArgumentSynthesizer implements Closeable {
	protected final Logger mLogger;

	public static final long s_randomSeed = 80085;

	protected static final int s_num_of_simultaneous_simplification_tests = 4;

	/**
	 * The SMT script for argument synthesis
	 */
	protected final Script m_script;

	/**
	 * The lasso program that we are analyzing
	 */
	protected final Lasso m_lasso;

	/**
	 * Preferences
	 */
	protected final LassoRankerPreferences m_preferences;

	/**
	 * Whether synthesize() has been called
	 */
	private boolean m_synthesis_successful = false;

	/**
	 * Whether close() has been called
	 */
	private boolean m_closed = false;

	
	protected IUltimateServiceProvider m_services;
	protected IToolchainStorage m_storage;
	
	/**
	 * Constructor for the argument synthesizer
	 * 
	 * @param lasso
	 *            the lasso program
	 * @param preferences
	 *            the preferences
	 * @param constaintsName
	 *            name of the constraints whose satisfiability is checked
	 * @param storage 
	 * @throws IOException 
	 */
	public ArgumentSynthesizer(Lasso lasso, LassoRankerPreferences preferences,
			String constaintsName, IUltimateServiceProvider services,
			IToolchainStorage storage) throws IOException {
		mLogger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_preferences = preferences;
		m_script = SMTSolver.newScript(preferences, constaintsName, services, storage);
		m_lasso = lasso;
		m_services = services;
		m_storage = storage;
	}

	/**
	 * @return the SMT script to be used for the argument synthesis
	 */
	public Script getScript() {
		return m_script;
	}

	/**
	 * @return whether the last call to synthesize() was successfull
	 */
	public boolean synthesisSuccessful() {
		return m_synthesis_successful;
	}

	/**
	 * Try to synthesize an argument for (non-)termination
	 * 
	 * @return result of the solver while checking the constraints
	 * @throws IOException 
	 */
	public final LBool synthesize() throws SMTLIBException, TermException, IOException {
		LBool lBool = do_synthesis();
		m_synthesis_successful = (lBool == LBool.SAT);
		return lBool;
	}

	/**
	 * Try to synthesize an argument for (non-)termination This is to be derived
	 * in the child classes and is wrapped by synthesize().
	 * 
	 * @return result of the solver while checking the constraints
	 * @throws IOException 
	 */
	protected abstract LBool do_synthesis() throws SMTLIBException, TermException, IOException;

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
	 * 
	 * @param variables
	 *            the list of variables that can be set to 0
	 * @return the number of pops required on m_script
	 */
	@Deprecated
	protected int simplifyAssignment(ArrayList<Term> variables) {
		// Shuffle the variable list for better effect
		Random rnd = new Random(s_randomSeed);
		Collections.shuffle(variables, rnd);

		int pops = 0;
		int checkSat_calls = 0;
		for (int i = 0; i < variables.size(); ++i) {
			Term var = variables.get(i);
			m_script.push(1);
			m_script.assertTerm(m_script.term("=", var, m_script.numeral(BigInteger.ZERO)));
			LBool sat = m_script.checkSat();
			++checkSat_calls;
			if (sat != LBool.SAT) {
				m_script.pop(1);
				// Make sure we call checkSat() after the last pop()
				if (i == variables.size() - 1) {
					sat = m_script.checkSat();
					++checkSat_calls;
					assert sat == LBool.SAT;
				}
			} else {
				pops += 1;
			}
		}
		mLogger.info("Simplification made " + checkSat_calls + " calls to the SMT solver.");
		return pops;
	}

	/**
	 * Tries to simplify a satisfying assignment by assigning zeros to
	 * variables. Gets stuck in local optima.
	 * 
	 * This is a more efficient version
	 * 
	 * @param variables
	 *            the list of variables that can be set to 0
	 * @return an assignment with (hopefully) many zeros
	 * @throws TermException
	 *             if model extraction fails
	 */
	protected Map<Term, Rational> getSimplifiedAssignment(ArrayList<Term> variables) throws TermException {
		Random rnd = new Random(s_randomSeed);
		Term zero = m_script.numeral("0");
		Map<Term, Rational> val = getValuation(variables);

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
			m_script.push(1);
			for (Term var : zero_vars) {
				m_script.assertTerm(m_script.term("=", var, zero));
			}
			for (int i = 0; i < 10; ++i) { // 10 is a good number
				List<Term> vars = new ArrayList<Term>(not_zero_vars);
				// Shuffle the variable list for better effect
				Collections.shuffle(vars, rnd);

				Term[] disj = new Term[s_num_of_simultaneous_simplification_tests];
				for (int j = 0; j < s_num_of_simultaneous_simplification_tests; ++j) {
					disj[j] = m_script.term("=", vars.get(j), zero);
				}
				m_script.assertTerm(Util.or(m_script, disj));
			}
			++checkSat_calls;
			LBool sat = m_script.checkSat();
			if (sat == LBool.SAT) {
				val = getValuation(not_zero_vars);
			} else {
				++unsat_calls;
				if (unsat_calls > 1) {
					// too many unsuccessful calls, so give up
					m_script.pop(1);
					break;
				}
			}
			m_script.pop(1);
		}

		// Add zero variables to the valuation
		for (Term var : zero_vars) {
			val.put(var, Rational.ZERO);
		}

		// Send stats to the logger
		mLogger.info("Simplification made " + checkSat_calls + " calls to the SMT solver.");
		int num_zero_vars = 0;
		for (Map.Entry<Term, Rational> entry : val.entrySet()) {
			if (entry.getValue().equals(Rational.ZERO)) {
				++num_zero_vars;
			}
		}
		mLogger.info("Setting " + num_zero_vars + " variables to zero.");

		return val;
	}

	/**
	 * Define a new constant
	 * 
	 * @param name
	 *            name of the new constant
	 * @param sort
	 *            the sort of the variable
	 * @return the new variable as a term
	 * @throws SMTLIBException
	 *             if something goes wrong, e.g. the name is already defined
	 */
	public Term newConstant(String name, String sortname) throws SMTLIBException {
		return SMTSolver.newConstant(m_script, name, sortname);
	}

	/**
	 * Convert a BigDecimal into a Rational. Stolen from Jochen's code
	 * de.uni_freiburg.informatik.ultimate.smtinterpol.convert.ConvertFormula.
	 */
	private static Rational decimalToRational(BigDecimal d) {
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
	 * Convert a constant term to Rational Extracts the value of the number from
	 * the term
	 * 
	 * @param ct
	 *            constant term
	 * @return rational from the value of ct
	 */
	static Rational convertCT(ConstantTerm ct) throws TermException {
		if (ct.getSort().getName().equals("Rational")) {
			return (Rational) ct.getValue();
		} else if (ct.getSort().getName().equals("Real")) {
			BigDecimal d = (BigDecimal) ct.getValue();
			return decimalToRational(d);
		} else if (ct.getSort().getName().equals("Int")) {
			if (ct.getValue() instanceof Rational) {
				return (Rational) ct.getValue();
			} else {
				Rational r = Rational.valueOf((BigInteger) ct.getValue(), BigInteger.ONE);
				return r;
			}
		} else
			throw new TermException("Trying to convert a ConstantTerm of unknown sort.", ct);
	}

	/**
	 * Convert a constant term retrieved from a model valuation to a Rational
	 * 
	 * @param t
	 *            a term containing only +, -, *, / and numerals
	 * @return the rational represented by the term
	 * @throws TermException
	 *             if an error occurred while parsing the term
	 */
	protected static Rational const2Rational(Term t) throws TermException {
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
	 * @param vars
	 *            a collection of variables
	 * @return a valuation that assigns a Rational to every variable
	 * @throws TermException
	 *             if valuation generation or conversion fails
	 */
	protected Map<Term, Rational> getValuation(Collection<Term> vars) throws TermException {
		// assert m_script.checkSat() == LBool.SAT;
		Map<Term, Term> val = m_script.getValue(vars.toArray(new Term[vars.size()]));
		Map<Term, Rational> result = new LinkedHashMap<Term, Rational>();
		for (Map.Entry<Term, Term> entry : val.entrySet()) {
			result.put(entry.getKey(), const2Rational(entry.getValue()));
		}
		return result;
	}

	/**
	 * Perform cleanup actions
	 */
	public void close() {
		if (!m_closed) {
			m_script.exit();
			m_closed = true;
		}
	}

	protected void finalize() {
		// Finalize methods are discouraged in Java.
		// Always call close() as exported by the Closable interface!
		// This is just a fallback to make sure close() has been called.
		this.close();
	}
}
