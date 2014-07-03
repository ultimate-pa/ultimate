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

import java.io.Closeable;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;


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
	protected static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	public static final long s_randomSeed = 80085;
	
	/**
	 * The SMT script for argument synthesis
	 */
	protected final Script m_script;
	
	/**
	 * The lasso's stem transition
	 */
	protected final LinearTransition m_stem;
	
	/**
	 * The lasso's loop transition
	 */
	protected final LinearTransition m_loop;
	
	/**
	 * Preferences
	 */
	protected final Preferences m_preferences;
	
	/**
	 * Whether synthesize() has been called
	 */
	private boolean m_synthesis_successful = false;
	
	/**
	 * Whether close() has been called
	 */
	private boolean m_closed = false;
	
	
	/**
	 * Constructor for the argument synthesizer
	 * 
	 * @param stem the lasso's stem transition
	 * @param loop the lasso's loop transition
	 * @param preferences the preferences
	 * @param constaintsName name of the constraints whose satisfiability is 
	 *                       checked
	 */
	public ArgumentSynthesizer(LinearTransition stem, LinearTransition loop,
			Preferences preferences, String constaintsName) {
		m_preferences = preferences;
		m_script = SMTSolver.newScript(preferences, constaintsName);
		
		if (stem == null) {
			m_stem = LinearTransition.getTranstionTrue();
		} else {
			m_stem = stem;
		}
		assert loop != null;
		m_loop = loop;
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
	 * @return result of the solver while checking the constraints
	 */
	public final LBool synthesize() throws SMTLIBException, TermException {
		LBool lBool = do_synthesis();
		m_synthesis_successful = (lBool == LBool.SAT);
		return lBool;
	}
	
	/**
	 * Try to synthesize an argument for (non-)termination
	 * This is to be derived in the child classes and is wrapped by
	 * synthesize().
	 * @return result of the solver while checking the constraints
	 */
	protected abstract LBool do_synthesis()
			throws SMTLIBException, TermException;
	
	/**
	 * Tries to simplify a satisfying assignment by assigning zeros to
	 * variables. Gets stuck in local optima.
	 * 
	 * The procedure works according to this principle:
	 * <pre>
	 * random.shuffle(variables)
	 * for v in variables:
	 *     if sat with v = 0:
	 *         set v to 0
	 * </pre>
	 * 
	 * @param variables the list of variables that can be set to 0
	 * @return the number of pops required on m_script
	 */
	protected int simplifyAssignment(ArrayList<Term> variables) {
		// Shuffle the variable list for better effect
		Random rnd =  new Random(s_randomSeed);
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
		s_Logger.info("Simplification made " + checkSat_calls
				+ " calls to the SMT solver.");
		return pops;
	}
	
	/**
	 * @return all RankVars that occur in the program
	 */
	protected Collection<RankVar> getAllRankVars() {
		Collection<RankVar> rankVars = new LinkedHashSet<RankVar>();
		if (m_stem != null) {
			rankVars.addAll(m_stem.getInVars().keySet());
			rankVars.addAll(m_stem.getOutVars().keySet());
		}
		rankVars.addAll(m_loop.getInVars().keySet());
		rankVars.addAll(m_loop.getOutVars().keySet());
		return rankVars;
	}
	
	/**
	 * Provide guesses for eigenvalues of the loop.
	 * 
	 * This procedure is neither sound nor complete:
	 * there might be eigenvalues that are not found by this procedure and
	 * this procedure might return values that are not eigenvalues of the loop.
	 * 
	 * The result of this is used as guesses for Motzkin coefficients in the
	 * termination analysis and for lambda in the nontermination analysis.
	 * This allows us to handle some more complicated examples while relying
	 * only on linear constraint solving.
	 * 
	 * This method works as follows. If there is a statement
	 * <pre>x = 2*y + 5</pre> we guess the eigenvalue 2 if we can prove
	 * that the loop disjunct implies x = y.
	 * 
	 * The returned values always contain 0 and 1.
	 * 
	 * @param include_negative whether to include negative guesses
	 * @return an array of guesses for the loop's eigenvalues
	 */
	protected Rational[] guessEigenvalues(boolean include_negative) {
		Set<Rational> motzkin_coeffs = new HashSet<Rational>();
		motzkin_coeffs.add(Rational.ZERO);
		motzkin_coeffs.add(Rational.ONE);
		for (List<LinearInequality> polyhedron : m_loop.getPolyhedra()) {
			// Find aliases for variables
			Map<Term, Set<Term>> aliases = new HashMap<Term, Set<Term>>();
			for (LinearInequality li : polyhedron) {
				// If li is 0 <= a*x + b*y with a == -b and a != 0 != b
				// then put x -> y into aliases
				if (!li.isStrict() && li.getConstant().isZero()
						&& li.getVariables().size() == 2) {
					Term[] vars = li.getVariables().toArray(new Term[2]);
					AffineTerm at0 = li.getCoefficient(vars[0]);
					AffineTerm at1 = li.getCoefficient(vars[1]);
					assert !at0.isZero();
					assert !at1.isZero();
					if (at0.isConstant() && at1.isConstant()
							&& at0.getConstant().equals(at1.getConstant().negate())) {
						Term var0 = vars[0];
						Term var1 = vars[1];
						if (at0.getConstant().isNegative()) {
							// Swap var0 and var1
							Term var2 = var0;
							var0 = var1;
							var1 = var2;
						}
						if (!aliases.containsKey(var0)) {
							aliases.put(var0, new HashSet<Term>());
						}
						aliases.get(var0).add(var1);
					}
				}
			}
			
			for (Map.Entry<RankVar, Term> entry : m_loop.getOutVars().entrySet()) {
				RankVar rkVar = entry.getKey();
				Term outVar = entry.getValue();
				
				// Find possible aliases
				if (!m_loop.getInVars().containsKey(rkVar)) {
					continue;
				}
				List<Term> possible_inVars = new ArrayList<Term>();
				Term inVar = m_loop.getInVars().get(rkVar);
				possible_inVars.add(inVar);
				if (aliases.containsKey(inVar)) {
					for (Term aliasVar : aliases.get(inVar)) {
						if (aliases.containsKey(aliasVar)
								&& aliases.get(aliasVar).contains(inVar)) {
							possible_inVars.add(aliasVar);
						}
					}
				}
				
				for (LinearInequality li : polyhedron) {
					for (Term aliasVar : possible_inVars) {
						AffineTerm c_in = li.getCoefficient(aliasVar);
						AffineTerm c_out = li.getCoefficient(outVar);
						if (!c_in.isZero() && !c_out.isZero()) {
							// inVar and outVar occur in this linear inequality
							assert c_in.isConstant();
							assert c_out.isConstant();
							Rational eigenv =
									c_in.getConstant().div(c_out.getConstant()).negate();
							if (!eigenv.isNegative() || include_negative) {
								motzkin_coeffs.add(eigenv);
							}
						}
					}
				}
			}
		}
		return motzkin_coeffs.toArray(new Rational[0]);
	}
	
	/**
	 * Define a new constant
	 * @param name name of the new constant
	 * @param sort the sort of the variable
	 * @return the new variable as a term
	 * @throws SMTLIBException if something goes wrong, e.g. the name is
	 *          already defined
	 */
	public Term newConstant(String name, String sortname)
			throws SMTLIBException {
		return SMTSolver.newConstant(m_script, name, sortname);
	}
	
	/**
	 * Convert a BigDecimal into a Rational.
	 * Stolen from Jochen's code
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
			return decimalToRational(d);
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
	
	/**
	 * Extract a valuation from a script and convert ConstantTerms into
	 * Rationals
	 * @param vars a collection of variables
	 * @return a valuation that assigns a Rational to every variable
	 * @throws TermException if valuation generation or conversion fails
	 */
	protected Map<Term, Rational> getValuation(Collection<Term> vars)
			throws TermException {
//		assert m_script.checkSat() == LBool.SAT;
		Map<Term, Term> val = m_script.getValue(vars.toArray(new Term[0]));
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
