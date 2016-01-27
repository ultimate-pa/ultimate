/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.ArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.Lasso;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.ModelExtractionUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.SMTPrettyPrinter;
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
 * exists z, x, y_1, ..., y_n, lambda_1, ..., lambda_n, nu_1, ..., nu_n 
 *    A_stem * (z, x) <= b_stem
 * /\ A_loop * (x, x + y_1 + ... + y_n) <= b_loop
 * /\ A_loop * (y_i, lambda_i * y_i + nu_i * y_{i+1}) <= 0   for each i
 * </pre>
 * where n is the number of generalized eigenvectors and y_{n+1} := 0.
 * We assume 0 <= n <= number of variables.
 * 
 * This class can't be a RankingFunctionsTemplate because that class
 * makes a bunch of assumptions regarding how the constraints are generated,
 * including the mandatory use of Motzkin's Theorem.
 * 
 * @author Jan Leike
 */
public class NonTerminationArgumentSynthesizer extends ArgumentSynthesizer {
	private static final String s_prefix_init = "init_";    // z
	private static final String s_prefix_honda = "honda_";  // x
	private static final String s_prefix_gevector = "gev_"; // y_i
	private static final String s_prefix_aux = "aux_";
	private static final String s_prefix_evalue = "lambda";   // lambda_i
	private static final String s_prefix_nilpotent = "nu";  // nu_i
	
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
		assert m_settings.number_of_gevs >= 0;
		String sort = m_integer_mode ? "Int" : "Real";
		
		// Create new variables
		Map<RankVar, Term> vars_init = new LinkedHashMap<RankVar, Term>();
		Map<RankVar, Term> vars_honda = new LinkedHashMap<RankVar, Term>();
		List<Map<RankVar, Term>> vars_gevs =
				new ArrayList<Map<RankVar, Term>>(m_settings.number_of_gevs);
		List<Term> lambdas = new ArrayList<Term>(m_settings.number_of_gevs);
		for (RankVar var : m_lasso.getAllRankVars()) {
			String name = SmtUtils.removeSmtQuoteCharacters(var.toString());
			vars_init.put(var, newConstant(s_prefix_init + name, sort));
			vars_honda.put(var, newConstant(s_prefix_honda + name, sort));
		}
		for (int i = 0; i < m_settings.number_of_gevs; ++i) {
			Map<RankVar, Term> vars_gev = new LinkedHashMap<RankVar, Term>();
			for (RankVar var : m_lasso.getAllRankVars()) {
				String name = SmtUtils.removeSmtQuoteCharacters(var.toString());
				vars_gev.put(var, newConstant(s_prefix_gevector + name + i, sort));
			}
			vars_gevs.add(vars_gev);
			lambdas.add(newConstant(s_prefix_evalue + i, sort));
		}
		List<Term> nus;
		if (m_settings.number_of_gevs > 0) {
			nus = new ArrayList<Term>(m_settings.number_of_gevs - 1);
			for (int i = 0; i < m_settings.number_of_gevs - 1; ++i) {
				nus.add(newConstant(s_prefix_nilpotent + i, sort));
			}
		} else {
			nus = Collections.emptyList();
		}
		
		Term constraints = generateConstraints(vars_init, vars_honda, vars_gevs,
				lambdas, nus);
		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(constraints)));
		m_script.assertTerm(constraints);
		
		// Check for satisfiability
		LBool isSat = m_script.checkSat();
		if (isSat == LBool.SAT) {
			m_argument = extractArgument(vars_init, vars_honda, vars_gevs,
					lambdas, nus);
		} else if (isSat == LBool.UNKNOWN) {
			m_script.echo(new QuotedObject(ArgumentSynthesizer.s_SolverUnknownMessage));
		}
		return isSat;
	}
	
	/**
	 * Generate the constraints corresponding to the nontermination argument
	 * 
	 * @param vars_init assignment before the stem (z)
	 * @param vars_honda assignment after the stem (x)
	 * @param vars_gevs variables for the generalized eigenvectors (y_i)
	 * @param lambdas variables for the eigenvalues
	 * @param nus variables for the nilpotent components
	 * @return the constraints
	 */
	public Term generateConstraints(Map<RankVar, Term> vars_init,
			Map<RankVar, Term> vars_honda, List<Map<RankVar, Term>> vars_gevs,
			List<Term> lambdas, List<Term> nus) {
		m_settings.checkSanity();
		assert m_settings.number_of_gevs >= 0;
		assert vars_gevs.size() == m_settings.number_of_gevs;
		assert lambdas.size() == m_settings.number_of_gevs;
		int num_vars;
		if (vars_gevs.isEmpty()) {
			num_vars = 0;
		} else {
			num_vars = vars_gevs.get(0).size();
		}
		assert num_vars >= 0;
		
		Collection<RankVar> rankVars = m_lasso.getAllRankVars();
		
		Term zero; // = 0
		Term one; // = 1
		if (!m_integer_mode) {
			zero = m_script.decimal("0");
			one = m_script.decimal("1");
		} else {
			zero = m_script.numeral("0");
			one = m_script.numeral("1");
		}
		
		List<Term> lambda_guesses; // possible guesses for lambda if we are generating linear constraints
		List<Term> nu_guesses; // possible values for nus
		if (m_analysis_type == AnalysisType.Nonlinear) {
			// Use a variable for lambda
			lambda_guesses = Collections.singletonList(null);
			nu_guesses = Collections.singletonList(null);
		} else {
			List<Term> l = new ArrayList<Term>();
			l.add(zero);
			l.add(one);
			nu_guesses = Collections.unmodifiableList(l);
			
			if (m_analysis_type == AnalysisType.Linear) {
				// Just use lambda = 1
				lambda_guesses = Collections.singletonList(one);
			} else if (m_analysis_type == AnalysisType.Linear_with_guesses) {
				// Use a list of guesses for lambda
				Rational[] eigenvalues = m_lasso.guessEigenvalues(false);
				lambda_guesses = new ArrayList<Term>(eigenvalues.length);
				for (int i = 0; i < eigenvalues.length; ++i) {
					assert !eigenvalues[i].isNegative();
					if (m_integer_mode && !eigenvalues[i].isIntegral()) {
						continue; // ignore non-integral guesses
					}
					lambda_guesses.add(eigenvalues[i].toTerm(m_sort));
				}
			} else {
				assert false; // unreachable branch
				lambda_guesses = Collections.emptyList();
			}
		}
		
		Term t1, t2, t3; // Three parts of the constraints
		
		// t1: A_stem * (z, x) <= b_stem
		t1 = m_script.term("true");
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
		
		// vars_end + vars_gevs
		Map<RankVar, Term> vars_end_plus_gevs =
				new LinkedHashMap<RankVar, Term>();
		vars_end_plus_gevs.putAll(vars_honda);
		for (RankVar rkVar : rankVars) {
			Term[] summands = new Term[m_settings.number_of_gevs + 1];
			summands[0] = vars_honda.get(rkVar);
			for (int i = 0; i < m_settings.number_of_gevs; ++i) {
				summands[i + 1] = vars_gevs.get(i).get(rkVar);
			}
			final Term sum;
			if (summands.length == 1) {
				sum = summands[0];
			} else {
				sum = m_script.term("+", summands);
			}
			vars_end_plus_gevs.put(rkVar, sum);
		}
		
		// vars_gev[i] * lambda_guesses + nu_i * vars_gev[i+1] for each i
		List<List<Map<RankVar, Term>>> vars_gevs_next =
				new ArrayList<List<Map<RankVar, Term>>>(m_settings.number_of_gevs);
		for (int i = 0; i < m_settings.number_of_gevs; ++i) {
			List<Map<RankVar, Term>> vars_gevs_next_i =
					new ArrayList<Map<RankVar, Term>>(lambda_guesses.size());
			vars_gevs_next.add(vars_gevs_next_i);
			for (int j = 0; j < lambda_guesses.size(); ++j) {
				for (int k = 0; k < nu_guesses.size(); ++k) {
					Term lambda_guess = lambda_guesses.get(j);
					if (lambda_guess == null) {
						lambda_guess = lambdas.get(i);
					}
					Term nu_guess = nu_guesses.get(k);
					if (nu_guess == null && i < m_settings.number_of_gevs - 1) {
						nu_guess = nus.get(i);
					}
					
					Map<RankVar, Term> gev_next = new LinkedHashMap<RankVar, Term>();
					vars_gevs_next_i.add(gev_next);
					for (RankVar rkVar : rankVars) {
						if (m_settings.nilpotent_components && i < m_settings.number_of_gevs - 1) {
							gev_next.put(rkVar, m_script.term("+",
								m_script.term("*", vars_gevs.get(i).get(rkVar), lambda_guess),
								m_script.term("*", vars_gevs.get(i + 1).get(rkVar), nu_guess)));
						} else {
							gev_next.put(rkVar, m_script.term("*",
									vars_gevs.get(i).get(rkVar), lambda_guess));
						}
					}
				}
			}
		}
		
		// t2: honda and rays
		{
			LinearTransition loop = m_lasso.getLoop();
			List<Term> disjunction = new ArrayList<Term>(loop.getNumPolyhedra());
			for (List<LinearInequality> polyhedron : loop.getPolyhedra()) {
				// A_loop * (x, x + y) <= b_loop
				Term t_honda = this.generateConstraint(loop, polyhedron,
						vars_honda, vars_end_plus_gevs, false);
				
				// A_loop * (y, lambda * y) <= 0
				Term[] conjuction = new Term[m_settings.number_of_gevs + 1];
				for (int i = 0; i < m_settings.number_of_gevs; ++i) {
					Term[] inner_disjunction = new Term[lambda_guesses.size()];
					for (int j = 0; j < lambda_guesses.size(); ++j) {
						Term lambda_guess = lambda_guesses.get(j);
						Term t_gev = this.generateConstraint(
								loop,
								polyhedron,
								vars_gevs.get(i),
								vars_gevs_next.get(i).get(j),
								true
						);
						Term fix_lambda;
						if (lambda_guess == null) {
							fix_lambda = m_script.term("true");
						} else {
							fix_lambda = m_script.term("=", lambdas.get(i), lambda_guess);
						}
						inner_disjunction[j] = Util.and(m_script, t_gev, fix_lambda);
					}
					conjuction[i] = Util.or(m_script, inner_disjunction);
				}
				conjuction[m_settings.number_of_gevs] = t_honda;
				disjunction.add(Util.and(m_script, conjuction));
			}
			t2 = Util.or(m_script, disjunction.toArray(new Term[0]));
		}
		
		// t3: constraints on the lambdas and the nus
		{
			List<Term> conjunction = new ArrayList<Term>(2*m_settings.number_of_gevs);
			
			// nu_i = 0 or nu_i = 1
			for (int i = 0; i < m_settings.number_of_gevs - 1; ++i) {
				Term nu = nus.get(i);
				conjunction.add(Util.or(m_script,
						m_script.term("=", nu, zero),
						m_script.term("=", nu, one)));
			}
			if (this.m_settings.allowBounded) {
				// lambda_i >= 0
				for (int i = 0; i < m_settings.number_of_gevs; ++i) {
					conjunction.add(m_script.term(">=", lambdas.get(i), zero));
				}
			} else {
				// lambda >= 1 and any vars_gev != 0;
				List<Term> disjunction =
						new ArrayList<Term>(m_settings.number_of_gevs*num_vars);
				for (int i = 0; i < m_settings.number_of_gevs; ++i) {
					for (Term t : vars_gevs.get(i).values()) {
						disjunction.add(m_script.term("<>", t, zero));
					}
					conjunction.add(m_script.term(">=", lambdas.get(i), one));
				}
				conjunction.add(Util.or(m_script, disjunction.toArray(new Term[0])));
			}
			t3 = Util.and(m_script, conjunction.toArray(new Term[0]));
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
			conjunction.add(m_script.term(rays ? ">=" : ieq.getInequalitySymbol(),
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
		Map<Term, Rational> val = ModelExtractionUtils.getValuation(m_script, vars.values());
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
			List<Map<RankVar, Term>> vars_gevs,
			List<Term> var_lambdas,
			List<Term> var_nus) {
//		assert m_script.checkSat() == LBool.SAT;
		
		try {
			Map<RankVar, Rational> state0 = extractState(vars_init);
			Map<RankVar, Rational> state1 = extractState(vars_honda);
			List<Map<RankVar, Rational>> gevs =
					new ArrayList<Map<RankVar, Rational>>(m_settings.number_of_gevs);
			final Map<Term, Term> lambda_val;
			if (var_lambdas.size() > 0) {
				lambda_val = m_script.getValue(var_lambdas.toArray(new Term[var_lambdas.size()]));
			} else {
				lambda_val = Collections.emptyMap();
			}
			final Map<Term, Term> nu_val;
			if (var_nus.size() > 0) {
				nu_val = m_script.getValue(var_nus.toArray(new Term[var_nus.size()]));
			} else {
				nu_val = Collections.emptyMap();
			}
			List<Rational> lambdas = new ArrayList<Rational>(m_settings.number_of_gevs);
			List<Rational> nus = new ArrayList<Rational>();
			for (int i = 0; i < m_settings.number_of_gevs; ++i) {
				gevs.add(extractState(vars_gevs.get(i)));
				lambdas.add(ModelExtractionUtils.const2Rational(
						lambda_val.get(var_lambdas.get(i))));
				if (i < m_settings.number_of_gevs - 1) {
					nus.add(ModelExtractionUtils.const2Rational(
						nu_val.get(var_nus.get(i))));
				}
			}
			boolean has_stem = !m_lasso.getStem().isTrue();
			return new NonTerminationArgument(has_stem ? state0 : state1,
					state1, gevs, lambdas, nus);
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
