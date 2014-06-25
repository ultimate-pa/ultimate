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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SmtUtils;


/**
 * The non-termination template checks for non-termination.
 * 
 * We check the following constraints.
 * <pre>
 * exists x0, x0', y
 *    A_stem * (x0, x0') <= b_stem
 * /\ A_loop * (x0', x0' + y) <= b_loop
 * /\ A_loop * (y, lambda * y) <= 0
 * </pre>
 * 
 * This class can't be a RankingFunctionsTemplate because that class
 * makes a bunch of assumptions regarding how the constraints are generated,
 * including the mandatory use of Motzkin's Theorem.
 * 
 * @author Jan Leike
 */
public class NonTerminationArgumentSynthesizer extends ArgumentSynthesizer {
	private static final String s_prefix_init = "init_";   // x0
	private static final String s_prefix_honda = "honda_"; // x0'
	private static final String s_prefix_ray = "ray_";     // y
	private static final String s_prefix_aux = "aux_";
	private static final String s_lambda_name = "lambda";  // lambda
	
	/**
	 * Counter for auxiliary variables
	 */
	public static long m_aux_counter = 0;
	
	/**
	 * Is the ray non-decreasing? (lambda = 1)
	 */
	private final boolean m_non_decreasing;
	
	/**
	 * Do we have to handle integers (QF_LIA logic)?
	 */
	private final boolean m_integer_mode;
	
	/**
	 * Contains the NonTerminationArgument object after successful discovery
	 */
	private NonTerminationArgument m_argument = null;
	
	/**
	 * Constructor for the termination argument function synthesizer.
	 * 
	 * @param stem the program stem
	 * @param loop the program loop
	 * @param preferences the preferences
	 */
	public NonTerminationArgumentSynthesizer(LinearTransition stem,
			LinearTransition loop, Preferences preferences) {
		super(stem, loop, preferences, "nonterminationTemplate");
		
		m_integer_mode = (stem != null && stem.containsIntegers())
				|| loop.containsIntegers();
		if (!m_integer_mode) {
			if (m_preferences.nontermination_check_nonlinear) {
				m_script.setLogic(Logics.QF_NRA);
			} else {
				m_script.setLogic(Logics.QF_LRA);
			}
		} else {
			s_Logger.info("Using integer mode.");
			if (m_preferences.nontermination_check_nonlinear) {
				s_Logger.warn("Integer program; non-termination SMT query must "
						+ "be linear!");
			}
			m_script.setLogic(Logics.QF_LIA);
		}
		m_non_decreasing =
				!m_preferences.nontermination_check_nonlinear || m_integer_mode;
	}
	
	@Override
	protected LBool do_synthesis() {
		String sort = m_integer_mode ? "Int" : "Real";
		
		// Create new variables
		Map<RankVar, Term> vars_init = new LinkedHashMap<RankVar, Term>();
		Map<RankVar, Term> vars_honda = new LinkedHashMap<RankVar, Term>();
		Map<RankVar, Term> vars_ray = new LinkedHashMap<RankVar, Term>();
		for (RankVar var : getAllRankVars()) {
			String name = SmtUtils.removeSmtQuoteCharacters(var.toString());
			vars_init.put(var, newConstant(s_prefix_init + name, sort));
			vars_honda.put(var,	newConstant(s_prefix_honda + name, sort));
			vars_ray.put(var, newConstant(s_prefix_ray + name, sort));
		}
		Term lambda = newConstant(s_lambda_name, sort);
		
		Term constraints = generateConstraints(vars_init, vars_honda, vars_ray,
				lambda);
		s_Logger.debug(SMTPrettyPrinter.print(constraints));
		m_script.assertTerm(constraints);
		
		// Check for satisfiability
		LBool isSat = m_script.checkSat();
		if (isSat == LBool.SAT) {
			m_argument = extractArgument(vars_init, vars_honda, vars_ray,
					lambda);
		} else if (isSat == LBool.UNKNOWN) {
			m_script.echo(new QuotedObject(SMTSolver.s_SolverUnknownMessage));
		}
		return isSat;
	}
	
	/**
	 * Generate the constraints corresponding to the nontermination argument
	 * @param vars_init 
	 * @param vars_honda
	 * @param vars_ray
	 * @param lambda
	 * @return
	 */
	public Term generateConstraints(Map<RankVar, Term> vars_init,
			Map<RankVar, Term> vars_honda, Map<RankVar, Term> vars_ray,
			Term lambda) {
		Collection<RankVar> rankVars = getAllRankVars();
		
		// A_stem * (x0, x0') <= b_stem
		Term t1 = m_script.term("true");
		if (m_stem != null) {
			List<Term> disjunction = new ArrayList<Term>(m_stem.getNumPolyhedra());
			for (List<LinearInequality> polyhedron : m_stem.getPolyhedra()) {
				disjunction.add(generateConstraint(
						m_stem,
						polyhedron,
						vars_init,
						vars_honda,
						false
				));
			}
			t1 = Util.or(m_script, disjunction.toArray(new Term[0]));
		}
		
		// vars_end + vars_ray
		Map<RankVar, Term> vars_end_plus_ray =
				new LinkedHashMap<RankVar, Term>();
		vars_end_plus_ray.putAll(vars_honda);
		for (RankVar rkVar : rankVars) {
			vars_end_plus_ray.put(rkVar,
					m_script.term("+", vars_honda.get(rkVar),
							vars_ray.get(rkVar)));
		}
		// vars_ray * lambda
		Map<RankVar, Term> vars_ray_times_lambda =
				new LinkedHashMap<RankVar, Term>();
		if (!m_non_decreasing) {
			for (RankVar rkVar : rankVars) {
				vars_ray_times_lambda.put(rkVar,
						m_script.term("*", vars_ray.get(rkVar), lambda));
			}
		}
		
		List<Term> disjunction = new ArrayList<Term>(m_loop.getNumPolyhedra());
		for (List<LinearInequality> polyhedron : m_loop.getPolyhedra()) {
			// A_loop * (x0', x0' + y) <= b_loop
			Term t_honda = this.generateConstraint(m_loop, polyhedron,
					vars_honda, vars_end_plus_ray, false);
			
			// A_loop * (y, lambda * y) <= 0
			Term t_ray = this.generateConstraint(
					m_loop,
					polyhedron,
					vars_ray,
					m_non_decreasing ? vars_ray : vars_ray_times_lambda,
					true
			);
			disjunction.add(Util.and(m_script, t_honda, t_ray));
		}
		Term t2 = Util.or(m_script, disjunction.toArray(new Term[0]));
		
		Term t3;
		if (!m_non_decreasing) {
			// lambda >= 0
			t3 = m_script.term(">=", lambda, m_script.decimal("0"));
		} else {
			t3 = m_script.term("=", lambda,
				m_integer_mode ? m_script.numeral(BigInteger.ONE)
							: m_script.decimal("1"));
		}
		return m_script.term("and", t1, t2, t3);
	}
	
	private Term generateConstraint(LinearTransition transition,
			List<LinearInequality> polyhedron,
			Map<RankVar, Term> varsIn,
			Map<RankVar, Term> varsOut,
			boolean rays) {
		Map<Term, Term> auxVars = new LinkedHashMap<Term, Term>();
		List<Term> conjunction = new ArrayList<Term>(polyhedron.size());
		for (LinearInequality ieq : polyhedron) {
			List<Term> summands = new ArrayList<Term>();
			Collection<Term> added_vars = new LinkedHashSet<Term>();
			
			// outVars
			for (Map.Entry<RankVar, Term> entry :
					transition.getOutVars().entrySet()) {
				if (!varsOut.containsKey(entry.getKey())) {
					continue;
				}
				AffineTerm a = ieq.getCoefficient(entry.getValue());
				summands.add(m_script.term("*", varsOut.get(entry.getKey()),
					m_integer_mode ? a.asIntTerm(m_script)
							: a.asRealTerm(m_script)));
				added_vars.add(entry.getValue());
			}
			
			// inVars
			for (Map.Entry<RankVar, Term> entry :
					transition.getInVars().entrySet()) {
				if (added_vars.contains(entry.getValue())) {
					// the transition implicitly requires that
					// entry.getKey() is constant
					conjunction.add(m_script.term(
							"=",
							varsIn.get(entry.getKey()),
							varsOut.get(entry.getKey())
					));
					continue;
				}
				AffineTerm a = ieq.getCoefficient(entry.getValue());
				summands.add(m_script.term("*", varsIn.get(entry.getKey()),
						m_integer_mode ? a.asIntTerm(m_script)
								: a.asRealTerm(m_script)));
				added_vars.add(entry.getValue());
			}
			
			// tmpVars
			Set<Term> all_vars = new LinkedHashSet<Term>(ieq.getVariables());
			all_vars.removeAll(added_vars);
			for (Term var : all_vars) {
				Term v;
				if (auxVars.containsKey(var)) {
					v = auxVars.get(var);
				} else {
					v = newConstant(s_prefix_aux + m_aux_counter,
							m_integer_mode ? "Int" : "Real");
					auxVars.put(var, v);
				}
				AffineTerm a = ieq.getCoefficient(var);
				summands.add(m_script.term("*", v,
						m_integer_mode ? a.asIntTerm(m_script)
								: a.asRealTerm(m_script)));
				++m_aux_counter;
			}
			if (!rays) {
				AffineTerm a = ieq.getConstant();
				summands.add(m_integer_mode ? a.asIntTerm(m_script)
						: a.asRealTerm(m_script));
			}
			conjunction.add(m_script.term(ieq.getInequalitySymbol(),
					SmtUtils.sum(m_script,
							m_integer_mode ? m_script.sort("Int")
									: m_script.sort("Real"),
							summands.toArray(new Term[0])),
					m_integer_mode ? m_script.numeral(BigInteger.ZERO)
							: m_script.decimal("0")));
		}
		return Util.and(m_script, conjunction.toArray(new Term[0]));
	}
	
	/**
	 * Extract a program state from the SMT script's model
	 * 
	 * @param vars a map from the program variables to corresponding SMT
	 *             variables
	 * @return the program state as a map from program variables to rational
	 *         numbers
	 */
	private Map<RankVar, Rational> extractState(Map<RankVar, Term> vars)
			throws SMTLIBException, UnsupportedOperationException,
			TermException {
		if (vars.isEmpty()) {
			return Collections.emptyMap();
		}
		Map<Term, Rational> val = getValuation(vars.values());
		// Concatenate vars and val
		Map<RankVar, Rational> state = new LinkedHashMap<RankVar, Rational>();
		for (Map.Entry<RankVar, Term> entry : vars.entrySet()) {
			assert(val.containsKey(entry.getValue()));
			state.put(entry.getKey(), val.get(entry.getValue()));
		}
		return state;
	}
	
	/**
	 * Extract the non-termination argument from a satisfiable script
	 * @return
	 * @throws SMTLIBException
	 */
	private NonTerminationArgument extractArgument(
			Map<RankVar, Term> vars_init,
			Map<RankVar, Term> vars_honda,
			Map<RankVar, Term> vars_ray,
			Term var_lambda) {
//		assert m_script.checkSat() == LBool.SAT;
		
		try {
			Map<RankVar, Rational> state0 = extractState(vars_init);
			Map<RankVar, Rational> state1 = extractState(vars_honda);
			Map<RankVar, Rational> ray = extractState(vars_ray);
			Rational lambda = const2Rational(
					m_script.getValue(new Term[] {var_lambda}).get(var_lambda));
			return new NonTerminationArgument(m_stem != null ? state0 : state1,
					state1, ray, lambda);
		} catch (UnsupportedOperationException e) {
			// do nothing
		} catch (TermException e) {
			// do nothing
		}
		return null;
	}
	
	/**
	 * @return the non-termination argument discovered
	 */
	public NonTerminationArgument getArgument() {
		assert synthesisSuccessful();
		return m_argument;
	}
}
