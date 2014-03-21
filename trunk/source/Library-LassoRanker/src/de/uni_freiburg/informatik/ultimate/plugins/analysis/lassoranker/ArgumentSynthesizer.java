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
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
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
public abstract class ArgumentSynthesizer {
	protected static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
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
	 * Whether synthesize() has been called yet
	 */
	private boolean m_synthesis_successful = false;
	
	/**
	 * @param script the SMT script to be used for the argument synthesis
	 * @param stem the lasso's stem transition
	 * @param loop the lasso's loop transition
	 */
	public ArgumentSynthesizer(Script script, LinearTransition stem,
			LinearTransition loop) {
		assert script != null;
		m_script = script;
		
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
	 * @return whether the synthesis was successful
	 */
	public final boolean synthesize() throws SMTLIBException, TermException {
		boolean success = do_synthesis();
		m_synthesis_successful = success;
		return success;
	}
	
	/**
	 * Try to synthesize an argument for (non-)termination
	 * This is to be derived in the child classes and is wrapped by
	 * synthesize().
	 * @return whether the synthesis was successful
	 */
	protected abstract boolean do_synthesis()
			throws SMTLIBException, TermException;
	
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
	 * Define a new constant
	 * @param name name of the new constant
	 * @param sort the sort of the variable
	 * @return the new variable as a term
	 * @throws SMTLIBException if something goes wrong, e.g. the name is
	 *          already defined
	 */
	public Term newConstant(String name, String sortname)
			throws SMTLIBException {
		return newConstant(m_script, name, sortname);
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
		assert m_script.checkSat() == LBool.SAT;
		Map<Term, Term> val = m_script.getValue(vars.toArray(new Term[0]));
		Map<Term, Rational> result = new LinkedHashMap<Term, Rational>();
		for (Map.Entry<Term, Term> entry : val.entrySet()) {
			result.put(entry.getKey(), const2Rational(entry.getValue()));
		}
		return result;
	}
}
