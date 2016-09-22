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

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
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
	public static long maux_counter = 0;
	
	/**
	 * Do we have to handle integers (QF_LIA logic)?
	 */
	private final boolean minteger_mode;
	
	/**
	 * What analysis type should be used for the nontermination analysis?
	 * Use a linear SMT query, use a linear SMT query but guess some eigenvalues
	 * of the loop, or use a nonlinear SMT query?
	 */
	private final AnalysisType manalysis_type;
	
	/**
	 * The settings for termination analysis
	 */
	private final NonTerminationAnalysisSettings msettings;
	
	/**
	 * The corresponding preferred sort ("Int" or "Real")
	 */
	private final Sort msort;
	
	/**
	 * Contains the NonTerminationArgument object after successful discovery
	 */
	private GeometricNonTerminationArgument margument = null;
	
	/**
	 * Result of SMT query
	 */
	private LBool mIsSat;
	
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
	public NonTerminationArgumentSynthesizer(final Lasso lasso,
			final LassoRankerPreferences preferences,
			final NonTerminationAnalysisSettings settings, final IUltimateServiceProvider services, final IToolchainStorage storage) throws IOException {
		super(lasso, preferences, "nonterminationTemplate", services, storage);
		
		msettings = new NonTerminationAnalysisSettings(settings); // defensive copy
		mLogger.info(settings.toString());
		
		minteger_mode = (lasso.getStem().containsIntegers())
				|| lasso.getLoop().containsIntegers();
		if (!minteger_mode) {
			manalysis_type = msettings.analysis;
			if (manalysis_type.isLinear()) {
				mscript.setLogic(Logics.QF_LRA);
			} else {
				mscript.setLogic(Logics.QF_NRA);
			}
			msort = mscript.sort("Real");
		} else {
			mLogger.info("Using integer mode.");
			manalysis_type = msettings.analysis;
			if (msettings.analysis.isLinear()) {
				mscript.setLogic(Logics.QF_LIA);
			} else {
				mscript.setLogic(Logics.QF_NIA);
			}
			msort = mscript.sort("Int");
		}
		assert !manalysis_type.isDisabled();
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	protected Script constructScript(final LassoRankerPreferences preferences, final String constraintsName) {
		final Settings settings = preferences.getSolverConstructionSettings(
				preferences.mBaseNameOfDumpedScript + "+" + constraintsName);
		final SolverMode solverMode;
		if (preferences.mAnnotateTerms) {
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
		} else {
			solverMode = SolverMode.External_ModelsMode;
		}
		final String solverId = "NonTerminationArgumentSynthesis solver ";
		return SolverBuilder.buildAndInitializeSolver(mservices, mstorage,
				solverMode, settings,
				false, false, null, solverId);
	}
	
	
	@Override
	protected LBool do_synthesis() {
		assert msettings.number_of_gevs >= 0;
		final String sort = minteger_mode ? "Int" : "Real";
		
		// Create new variables
		final Map<IProgramVar, Term> vars_init = new LinkedHashMap<IProgramVar, Term>();
		final Map<IProgramVar, Term> vars_honda = new LinkedHashMap<IProgramVar, Term>();
		final List<Map<IProgramVar, Term>> vars_gevs =
				new ArrayList<Map<IProgramVar, Term>>(msettings.number_of_gevs);
		final List<Term> lambdas = new ArrayList<Term>(msettings.number_of_gevs);
		for (final IProgramVar var : mlasso.getAllRankVars()) {
			final String name = SmtUtils.removeSmtQuoteCharacters(var.toString());
			vars_init.put(var, newConstant(s_prefix_init + name, sort));
			vars_honda.put(var, newConstant(s_prefix_honda + name, sort));
		}
		for (int i = 0; i < msettings.number_of_gevs; ++i) {
			final Map<IProgramVar, Term> vars_gev = new LinkedHashMap<IProgramVar, Term>();
			for (final IProgramVar var : mlasso.getAllRankVars()) {
				final String name = SmtUtils.removeSmtQuoteCharacters(var.toString());
				vars_gev.put(var, newConstant(s_prefix_gevector + name + i, sort));
			}
			vars_gevs.add(vars_gev);
			lambdas.add(newConstant(s_prefix_evalue + i, sort));
		}
		List<Term> nus;
		if (msettings.number_of_gevs > 0) {
			nus = new ArrayList<Term>(msettings.number_of_gevs - 1);
			for (int i = 0; i < msettings.number_of_gevs - 1; ++i) {
				nus.add(newConstant(s_prefix_nilpotent + i, sort));
			}
		} else {
			nus = Collections.emptyList();
		}
		
		final Term constraints = generateConstraints(vars_init, vars_honda, vars_gevs,
				lambdas, nus);
		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(constraints)));
		mscript.assertTerm(constraints);
		
		// Check for satisfiability
		mIsSat = mscript.checkSat();
		if (mIsSat == LBool.SAT) {
			margument = extractArgument(vars_init, vars_honda, vars_gevs,
					lambdas, nus);
		} else if (mIsSat == LBool.UNKNOWN) {
			mscript.echo(new QuotedObject(ArgumentSynthesizer.s_SolverUnknownMessage));
		}
		return mIsSat;
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
	public Term generateConstraints(final Map<IProgramVar, Term> vars_init,
			final Map<IProgramVar, Term> vars_honda, final List<Map<IProgramVar, Term>> vars_gevs,
			final List<Term> lambdas, final List<Term> nus) {
		msettings.checkSanity();
		assert msettings.number_of_gevs >= 0;
		assert vars_gevs.size() == msettings.number_of_gevs;
		assert lambdas.size() == msettings.number_of_gevs;
		int numvars;
		if (vars_gevs.isEmpty()) {
			numvars = 0;
		} else {
			numvars = vars_gevs.get(0).size();
		}
		assert numvars >= 0;
		
		final Collection<IProgramVar> rankVars = mlasso.getAllRankVars();
		
		Term zero; // = 0
		Term one; // = 1
		if (!minteger_mode) {
			zero = mscript.decimal("0");
			one = mscript.decimal("1");
		} else {
			zero = mscript.numeral("0");
			one = mscript.numeral("1");
		}
		
		List<Term> lambda_guesses; // possible guesses for lambda if we are generating linear constraints
		List<Term> nu_guesses; // possible values for nus
		if (manalysis_type == AnalysisType.Nonlinear) {
			// Use a variable for lambda
			lambda_guesses = Collections.singletonList(null);
			nu_guesses = Collections.singletonList(null);
		} else {
			final List<Term> l = new ArrayList<Term>();
			l.add(zero);
			l.add(one);
			nu_guesses = Collections.unmodifiableList(l);
			
			if (manalysis_type == AnalysisType.Linear) {
				// Just use lambda = 1
				lambda_guesses = Collections.singletonList(one);
			} else if (manalysis_type == AnalysisType.Linear_with_guesses) {
				// Use a list of guesses for lambda
				final Rational[] eigenvalues = mlasso.guessEigenvalues(false);
				lambda_guesses = new ArrayList<Term>(eigenvalues.length);
				for (int i = 0; i < eigenvalues.length; ++i) {
					assert !eigenvalues[i].isNegative();
					if (minteger_mode && !eigenvalues[i].isIntegral()) {
						continue; // ignore non-integral guesses
					}
					lambda_guesses.add(eigenvalues[i].toTerm(msort));
				}
			} else {
				assert false; // unreachable branch
				lambda_guesses = Collections.emptyList();
			}
		}
		
		Term t1, t2, t3; // Three parts of the constraints
		
		// t1: A_stem * (z, x) <= b_stem
		t1 = mscript.term("true");
		if (!mlasso.getStem().isTrue()) {
			final LinearTransition stem = mlasso.getStem();
			final List<Term> disjunction = new ArrayList<Term>(stem.getNumPolyhedra());
			for (final List<LinearInequality> polyhedron : stem.getPolyhedra()) {
				disjunction.add(generateConstraint(
						stem,
						polyhedron,
						vars_init,
						vars_honda,
						false
				));
			}
			t1 = Util.or(mscript, disjunction.toArray(new Term[disjunction.size()]));
		}
		
		// vars_end + vars_gevs
		final Map<IProgramVar, Term> vars_end_plus_gevs =
				new LinkedHashMap<IProgramVar, Term>();
		vars_end_plus_gevs.putAll(vars_honda);
		for (final IProgramVar rkVar : rankVars) {
			final Term[] summands = new Term[msettings.number_of_gevs + 1];
			summands[0] = vars_honda.get(rkVar);
			for (int i = 0; i < msettings.number_of_gevs; ++i) {
				summands[i + 1] = vars_gevs.get(i).get(rkVar);
			}
			final Term sum;
			if (summands.length == 1) {
				sum = summands[0];
			} else {
				sum = mscript.term("+", summands);
			}
			vars_end_plus_gevs.put(rkVar, sum);
		}
		
		// vars_gev[i] * lambda_guesses + nu_i * vars_gev[i+1] for each i
		final List<List<Map<IProgramVar, Term>>> vars_gevs_next =
				new ArrayList<List<Map<IProgramVar, Term>>>(msettings.number_of_gevs);
		for (int i = 0; i < msettings.number_of_gevs; ++i) {
			final List<Map<IProgramVar, Term>> vars_gevs_next_i =
					new ArrayList<Map<IProgramVar, Term>>(lambda_guesses.size());
			vars_gevs_next.add(vars_gevs_next_i);
			for (int j = 0; j < lambda_guesses.size(); ++j) {
				for (int k = 0; k < nu_guesses.size(); ++k) {
					Term lambda_guess = lambda_guesses.get(j);
					if (lambda_guess == null) {
						lambda_guess = lambdas.get(i);
					}
					Term nu_guess = nu_guesses.get(k);
					if (nu_guess == null && i < msettings.number_of_gevs - 1) {
						nu_guess = nus.get(i);
					}
					
					final Map<IProgramVar, Term> gev_next = new LinkedHashMap<IProgramVar, Term>();
					vars_gevs_next_i.add(gev_next);
					for (final IProgramVar rkVar : rankVars) {
						if (msettings.nilpotent_components && i < msettings.number_of_gevs - 1) {
							gev_next.put(rkVar, mscript.term("+",
								mscript.term("*", vars_gevs.get(i).get(rkVar), lambda_guess),
								mscript.term("*", vars_gevs.get(i + 1).get(rkVar), nu_guess)));
						} else {
							gev_next.put(rkVar, mscript.term("*",
									vars_gevs.get(i).get(rkVar), lambda_guess));
						}
					}
				}
			}
		}
		
		// t2: honda and rays
		{
			final LinearTransition loop = mlasso.getLoop();
			final List<Term> disjunction = new ArrayList<Term>(loop.getNumPolyhedra());
			for (final List<LinearInequality> polyhedron : loop.getPolyhedra()) {
				// A_loop * (x, x + y) <= b_loop
				final Term t_honda = generateConstraint(loop, polyhedron,
						vars_honda, vars_end_plus_gevs, false);
				
				// A_loop * (y, lambda * y) <= 0
				final Term[] conjuction = new Term[msettings.number_of_gevs + 1];
				for (int i = 0; i < msettings.number_of_gevs; ++i) {
					final Term[] inner_disjunction = new Term[lambda_guesses.size()];
					for (int j = 0; j < lambda_guesses.size(); ++j) {
						final Term lambda_guess = lambda_guesses.get(j);
						final Term t_gev = generateConstraint(
								loop,
								polyhedron,
								vars_gevs.get(i),
								vars_gevs_next.get(i).get(j),
								true
						);
						Term fix_lambda;
						if (lambda_guess == null) {
							fix_lambda = mscript.term("true");
						} else {
							fix_lambda = mscript.term("=", lambdas.get(i), lambda_guess);
						}
						inner_disjunction[j] = Util.and(mscript, t_gev, fix_lambda);
					}
					conjuction[i] = Util.or(mscript, inner_disjunction);
				}
				conjuction[msettings.number_of_gevs] = t_honda;
				disjunction.add(Util.and(mscript, conjuction));
			}
			t2 = Util.or(mscript, disjunction.toArray(new Term[disjunction.size()]));
		}
		
		// t3: constraints on the lambdas and the nus
		{
			final List<Term> conjunction = new ArrayList<Term>(2*msettings.number_of_gevs);
			
			// nu_i = 0 or nu_i = 1
			for (int i = 0; i < msettings.number_of_gevs - 1; ++i) {
				final Term nu = nus.get(i);
				conjunction.add(Util.or(mscript,
						mscript.term("=", nu, zero),
						mscript.term("=", nu, one)));
			}
			if (msettings.allowBounded) {
				// lambda_i >= 0
				for (int i = 0; i < msettings.number_of_gevs; ++i) {
					conjunction.add(mscript.term(">=", lambdas.get(i), zero));
				}
			} else {
				// lambda >= 1 and any vars_gev != 0;
				final List<Term> disjunction =
						new ArrayList<Term>(msettings.number_of_gevs*numvars);
				for (int i = 0; i < msettings.number_of_gevs; ++i) {
					for (final Term t : vars_gevs.get(i).values()) {
						disjunction.add(mscript.term("<>", t, zero));
					}
					conjunction.add(mscript.term(">=", lambdas.get(i), one));
				}
				conjunction.add(Util.or(mscript, disjunction.toArray(new Term[disjunction.size()])));
			}
			t3 = Util.and(mscript, conjunction.toArray(new Term[conjunction.size()]));
		}

		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t1)));
		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t2)));
		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t3)));
		return mscript.term("and", t1, t2, t3);
	}
	
	private Term generateConstraint(final LinearTransition transition,
			final List<LinearInequality> polyhedron,
			final Map<IProgramVar, Term> varsIn,
			final Map<IProgramVar, Term> varsOut,
			final boolean rays) {
		final Map<Term, Term> auxVars = new LinkedHashMap<Term, Term>();
		final List<Term> conjunction = new ArrayList<Term>(polyhedron.size());
		for (final LinearInequality ieq : polyhedron) {
			final List<Term> summands = new ArrayList<Term>();
			final Collection<Term> added_vars = new LinkedHashSet<Term>();
			
			// outVars
			for (final Map.Entry<IProgramVar, Term> entry :
					transition.getOutVars().entrySet()) {
				if (!varsOut.containsKey(entry.getKey())) {
					continue;
				}
				final AffineTerm a = ieq.getCoefficient(entry.getValue());
				summands.add(mscript.term("*", varsOut.get(entry.getKey()),
					minteger_mode ? a.asIntTerm(mscript)
							: a.asRealTerm(mscript)));
				added_vars.add(entry.getValue());
			}
			
			// inVars
			for (final Map.Entry<IProgramVar, Term> entry :
					transition.getInVars().entrySet()) {
				if (added_vars.contains(entry.getValue())) {
					// the transition implicitly requires that
					// entry.getKey() is constant
					conjunction.add(mscript.term(
							"=",
							varsIn.get(entry.getKey()),
							varsOut.get(entry.getKey())
					));
					continue;
				}
				final AffineTerm a = ieq.getCoefficient(entry.getValue());
				summands.add(mscript.term("*", varsIn.get(entry.getKey()),
						minteger_mode ? a.asIntTerm(mscript)
								: a.asRealTerm(mscript)));
				added_vars.add(entry.getValue());
			}
			
			// tmpVars
			final Set<Term> all_vars = new LinkedHashSet<Term>(ieq.getVariables());
			all_vars.removeAll(added_vars);
			for (final Term var : all_vars) {
				Term v;
				if (auxVars.containsKey(var)) {
					v = auxVars.get(var);
				} else {
					v = newConstant(s_prefix_aux + maux_counter,
							minteger_mode ? "Int" : "Real");
					auxVars.put(var, v);
				}
				final AffineTerm a = ieq.getCoefficient(var);
				summands.add(mscript.term("*", v,
						minteger_mode ? a.asIntTerm(mscript)
								: a.asRealTerm(mscript)));
				++maux_counter;
			}
			if (!rays) {
				final AffineTerm a = ieq.getConstant();
				summands.add(minteger_mode ? a.asIntTerm(mscript)
						: a.asRealTerm(mscript));
			}
			conjunction.add(mscript.term(rays ? ">=" : ieq.getInequalitySymbol(),
					SmtUtils.sum(mscript, msort,
							summands.toArray(new Term[summands.size()])),
					minteger_mode ? mscript.numeral(BigInteger.ZERO)
							: mscript.decimal("0")));
		}
		return Util.and(mscript, conjunction.toArray(new Term[conjunction.size()]));
	}
	
	/**
	 * Extract a program state from the SMT script's model
	 * 
	 * @param vars a map from the program variables to corresponding SMT
	 *             variables
	 * @return the program state as a map from program variables to rational
	 *         numbers
	 */
	private Map<IProgramVar, Rational> extractState(final Map<IProgramVar, Term> vars)
			throws SMTLIBException, UnsupportedOperationException,
			TermException {
		if (vars.isEmpty()) {
			return Collections.emptyMap();
		}
		final Map<Term, Rational> val = ModelExtractionUtils.getValuation(mscript, vars.values());
		// Concatenate vars and val
		final Map<IProgramVar, Rational> state = new LinkedHashMap<IProgramVar, Rational>();
		for (final Map.Entry<IProgramVar, Term> entry : vars.entrySet()) {
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
	private GeometricNonTerminationArgument extractArgument(
			final Map<IProgramVar, Term> vars_init,
			final Map<IProgramVar, Term> vars_honda,
			final List<Map<IProgramVar, Term>> vars_gevs,
			final List<Term> var_lambdas,
			final List<Term> var_nus) {
//		assert mscript.checkSat() == LBool.SAT;
		
		try {
			final Map<IProgramVar, Rational> state0 = extractState(vars_init);
			final Map<IProgramVar, Rational> state1 = extractState(vars_honda);
			final List<Map<IProgramVar, Rational>> gevs =
					new ArrayList<Map<IProgramVar, Rational>>(msettings.number_of_gevs);
			final Map<Term, Term> lambda_val;
			if (!var_lambdas.isEmpty()) {
				lambda_val = mscript.getValue(var_lambdas.toArray(new Term[var_lambdas.size()]));
			} else {
				lambda_val = Collections.emptyMap();
			}
			final Map<Term, Term> nu_val;
			if (!var_nus.isEmpty()) {
				nu_val = mscript.getValue(var_nus.toArray(new Term[var_nus.size()]));
			} else {
				nu_val = Collections.emptyMap();
			}
			final List<Rational> lambdas = new ArrayList<Rational>(msettings.number_of_gevs);
			final List<Rational> nus = new ArrayList<Rational>();
			for (int i = 0; i < msettings.number_of_gevs; ++i) {
				gevs.add(extractState(vars_gevs.get(i)));
				lambdas.add(ModelExtractionUtils.const2Rational(
						lambda_val.get(var_lambdas.get(i))));
				if (i < msettings.number_of_gevs - 1) {
					nus.add(ModelExtractionUtils.const2Rational(
						nu_val.get(var_nus.get(i))));
				}
			}
			final boolean has_stem = !mlasso.getStem().isTrue();
			return new GeometricNonTerminationArgument(has_stem ? state0 : state1,
					state1, gevs, lambdas, nus);
		} catch (final UnsupportedOperationException e) {
			// do nothing
		} catch (final TermException e) {
			// do nothing
		}
		return null;
	}
	
	/**
	 * @return the non-termination argument discovered
	 */
	public GeometricNonTerminationArgument getArgument() {
		assert synthesisSuccessful();
		return margument;
	}
	
}
