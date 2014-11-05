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
package de.uni_freiburg.informatik.ultimate.lassoranker.nontermination;

import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.ArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.Lasso;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.SMTPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.lassoranker.SMTSolver;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;


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
	 * Do we have to handle integers (QF_LIA logic)?
	 */
	private final boolean m_integer_mode;
	
	/**
	 * What analysis type should be used for the nontermination analysis?
	 * Use a linear SMT query, use a linear SMT query but guess some eigenvalues
	 * of the loop, or use a nonlinear SMT query?
	 */
	private final AnalysisType m_analysis_type;
	
	/**
	 * The settings for termination analysis
	 */
	private final NonTerminationAnalysisSettings m_settings;
	
	/**
	 * The corresponding preferred sort ("Int" or "Real")
	 */
	private final Sort m_sort;
	
	/**
	 * Contains the NonTerminationArgument object after successful discovery
	 */
	private NonTerminationArgument m_argument = null;
	
	/**
	 * Constructor for the termination argument function synthesizer.
	 * 
	 * @param lasso the lasso program
	 * @param preferences lasso ranker preferences
	 * @param settings (local) settings for termination analysis
	 * @param services 
	 * @param storage 
	 * @throws IOException 
	 */
	public NonTerminationArgumentSynthesizer(Lasso lasso,
			LassoRankerPreferences preferences,
			NonTerminationAnalysisSettings settings, IUltimateServiceProvider services, IToolchainStorage storage) throws IOException {
		super(lasso, preferences, "nonterminationTemplate", services, storage);
		
		m_settings = new NonTerminationAnalysisSettings(settings); // defensive copy
		mLogger.info(settings.toString());
		
		m_integer_mode = (lasso.getStem().containsIntegers())
				|| lasso.getLoop().containsIntegers();
		if (!m_integer_mode) {
			m_analysis_type = m_settings.analysis;
			if (m_analysis_type.isLinear()) {
				m_script.setLogic(Logics.QF_LRA);
			} else {
				m_script.setLogic(Logics.QF_NRA);
			}
			m_sort = m_script.sort("Real");
		} else {
			mLogger.info("Using integer mode.");
			m_analysis_type = m_settings.analysis;
			if (m_settings.analysis.isLinear()) {
				m_script.setLogic(Logics.QF_LIA);
			} else {
				m_script.setLogic(Logics.QF_NIA);
			}
			m_sort = m_script.sort("Int");
		}
		assert !m_analysis_type.isDisabled();
	}
	
	@Override
	protected LBool do_synthesis() {
		String sort = m_integer_mode ? "Int" : "Real";
		
		// Create new variables
		Map<RankVar, Term> vars_init = new LinkedHashMap<RankVar, Term>();
		Map<RankVar, Term> vars_honda = new LinkedHashMap<RankVar, Term>();
		Map<RankVar, Term> vars_ray = new LinkedHashMap<RankVar, Term>();
		for (RankVar var : m_lasso.getAllRankVars()) {
			String name = SmtUtils.removeSmtQuoteCharacters(var.toString());
			vars_init.put(var, newConstant(s_prefix_init + name, sort));
			vars_honda.put(var,	newConstant(s_prefix_honda + name, sort));
			vars_ray.put(var, newConstant(s_prefix_ray + name, sort));
		}
		Term lambda = newConstant(s_lambda_name, sort);
		
		Term constraints = generateConstraints(vars_init, vars_honda, vars_ray,
				lambda);
		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(constraints)));
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
	 * @return the constraints
	 */
	public Term generateConstraints(Map<RankVar, Term> vars_init,
			Map<RankVar, Term> vars_honda, Map<RankVar, Term> vars_ray,
			Term lambda) {
		Collection<RankVar> rankVars = m_lasso.getAllRankVars();
		
		List<Term> lambdas;
		if (m_analysis_type == AnalysisType.Linear) {
			// Just use lambda = 1
			Term one = m_script.numeral("1");
			lambdas = Collections.singletonList(one);
		} else if (m_analysis_type == AnalysisType.Linear_with_guesses) {
			// Use a list of guesses for lambda
			Rational[] eigenvalues = m_lasso.guessEigenvalues(false);
			lambdas = new ArrayList<Term>(eigenvalues.length);
			for (int i = 0; i < eigenvalues.length; ++i) {
				assert !eigenvalues[i].isNegative();
				if (m_integer_mode && !eigenvalues[i].isIntegral()) {
					continue; // ignore non-integral guesses
				}
				lambdas.add(eigenvalues[i].toTerm(m_sort));
			}
		} else {
			assert m_analysis_type == AnalysisType.Nonlinear;
			// Use a variable for lambda
			lambdas = Collections.singletonList(lambda);
		}
		
		// A_stem * (x0, x0') <= b_stem
		Term t1 = m_script.term("true");
		if (!m_lasso.getStem().isTrue()) {
			LinearTransition stem = m_lasso.getStem();
			List<Term> disjunction = new ArrayList<Term>(stem.getNumPolyhedra());
			for (List<LinearInequality> polyhedron : stem.getPolyhedra()) {
				disjunction.add(generateConstraint(
						stem,
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
		List<Map<RankVar, Term>> vars_ray_times_lambdas =
				new ArrayList<Map<RankVar, Term>>(lambdas.size());
		for (int i = 0; i < lambdas.size(); ++i) {
			Term lambda_t = lambdas.get(i);
			Map<RankVar, Term> ray_times_lambda = new LinkedHashMap<RankVar, Term>();
			vars_ray_times_lambdas.add(ray_times_lambda);
			for (RankVar rkVar : rankVars) {
				ray_times_lambda.put(rkVar,
						m_script.term("*", vars_ray.get(rkVar), lambda_t));
			}
		}
		
		LinearTransition loop = m_lasso.getLoop();
		List<Term> disjunction = new ArrayList<Term>(loop.getNumPolyhedra());
		for (List<LinearInequality> polyhedron : loop.getPolyhedra()) {
			// A_loop * (x0', x0' + y) <= b_loop
			Term t_honda = this.generateConstraint(loop, polyhedron,
					vars_honda, vars_end_plus_ray, false);
			
			// A_loop * (y, lambda * y) <= 0
			for (int i = 0; i < lambdas.size(); ++i) {
				Map<RankVar, Term> ray_times_lambda =
						vars_ray_times_lambdas.get(i);
				Term t_ray = this.generateConstraint(
						loop,
						polyhedron,
						vars_ray,
						ray_times_lambda,
						true
				);
				Term fix_lambda = m_script.term("=", lambda, lambdas.get(i));
				disjunction.add(Util.and(m_script, t_honda, t_ray, fix_lambda));
			}
		}
		Term t2 = Util.or(m_script, disjunction.toArray(new Term[0]));
		
		Term t3;
		if (!m_integer_mode) {
			// lambda >= 0
			t3 = m_script.term(">=", lambda, m_script.decimal("0"));
		} else {
			t3 = m_script.term("true");
		}

		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t1)));
		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t2)));
		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t3)));
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
					SmtUtils.sum(m_script, m_sort,
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
			boolean has_stem = !m_lasso.getStem().isTrue();
			return new NonTerminationArgument(has_stem ? state0 : state1,
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
