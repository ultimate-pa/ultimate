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

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.ArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.ILassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.Lasso;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.ModelExtractionUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

/**
 * The non-termination template checks for non-termination.
 *
 * We check the following constraints.
 *
 * <pre>
 * exists z, x, y_1, ..., y_n, lambda_1, ..., lambda_n, nu_1, ..., nu_n
 *    A_stem * (z, x) <= b_stem
 * /\ A_loop * (x, x + y_1 + ... + y_n) <= b_loop
 * /\ A_loop * (y_i, lambda_i * y_i + nu_i * y_{i+1}) <= 0   for each i
 * </pre>
 *
 * where n is the number of generalized eigenvectors and y_{n+1} := 0. We assume 0 <= n <= number of variables.
 *
 * This class can't be a RankingFunctionsTemplate because that class makes a bunch of assumptions regarding how the
 * constraints are generated, including the mandatory use of Motzkin's Theorem.
 *
 * @author Jan Leike
 */
public class NonTerminationArgumentSynthesizer extends ArgumentSynthesizer {
	private static final String PREFIX_INIT = "init_"; // z
	private static final String PREFIX_HONDA = "honda_"; // x
	private static final String PREFIX_GE_VECTOR = "gev_"; // y_i
	private static final String PREFIX_AUX = "aux_";
	private static final String PREFIX_EVALUE = "lambda"; // lambda_i
	private static final String PREFIX_NIL_POTENT = "nu"; // nu_i

	/**
	 * Counter for auxiliary variables
	 */
	public static long sAuxCounter = 0;

	/**
	 * Do we have to handle integers (QF_LIA logic)?
	 */
	private final boolean mIntegerMode;

	/**
	 * What analysis type should be used for the nontermination analysis? Use a linear SMT query, use a linear SMT query
	 * but guess some eigenvalues of the loop, or use a nonlinear SMT query?
	 */
	private final AnalysisType mAnalysisType;

	/**
	 * The settings for termination analysis
	 */
	private final NonTerminationAnalysisSettings mSettings;

	/**
	 * The corresponding preferred sort ("Int" or "Real")
	 */
	private final Sort mSort;

	/**
	 * Contains the NonTerminationArgument object after successful discovery
	 */
	private GeometricNonTerminationArgument mArgument;

	/**
	 * Result of SMT query
	 */
	private LBool mIsSat;

	/**
	 * Constructor for the termination argument function synthesizer.
	 *
	 * @param lasso
	 *            the lasso program
	 * @param preferences
	 *            lasso ranker preferences
	 * @param settings
	 *            (local) settings for termination analysis
	 * @param services
	 * @throws IOException
	 */
	public NonTerminationArgumentSynthesizer(final Lasso lasso, final ILassoRankerPreferences preferences,
			final NonTerminationAnalysisSettings settings, final IUltimateServiceProvider services) throws IOException {
		super(lasso, preferences, "nonterminationTemplate", services);
		mArgument = null;
		mSettings = new NonTerminationAnalysisSettings(settings); // defensive copy
		mLogger.info(settings.toString());

		mIntegerMode = (lasso.getStem().containsIntegers()) || lasso.getLoop().containsIntegers();
		if (!mIntegerMode) {
			mAnalysisType = mSettings.getAnalysis();
			if (mAnalysisType.isLinear()) {
				mScript.setLogic(Logics.QF_LRA);
			} else {
				mScript.setLogic(Logics.QF_NRA);
			}
			mSort = SmtSortUtils.getRealSort(mScript);
		} else {
			mLogger.info("Using integer mode.");
			mAnalysisType = mSettings.getAnalysis();
			if (mSettings.getAnalysis().isLinear()) {
				mScript.setLogic(Logics.QF_LIA);
			} else {
				mScript.setLogic(Logics.QF_NIA);
			}
			mSort = SmtSortUtils.getIntSort(mScript);
		}
		assert !mAnalysisType.isDisabled();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected Script constructScript(final ILassoRankerPreferences preferences, final String constraintsName) {
		final SolverSettings settings = preferences
				.getSolverConstructionSettings(preferences.getBaseNameOfDumpedScript() + "+" + constraintsName);
		final SolverMode solverMode;
		if (preferences.isAnnotateTerms()) {
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
		} else {
			solverMode = SolverMode.External_ModelsMode;
		}
		final String solverId = "NonTerminationArgumentSynthesis solver ";
		return SolverBuilder.buildAndInitializeSolver(mServices, solverMode, settings, false, false, null, solverId);
	}

	@Override
	protected LBool do_synthesis() {
		assert mSettings.getNumberOfGevs() >= 0;
		final String sort = mIntegerMode ? SmtSortUtils.INT_SORT : SmtSortUtils.REAL_SORT;

		// Create new variables
		final Map<IProgramVar, Term> vars_init = new LinkedHashMap<>();
		final Map<IProgramVar, Term> vars_honda = new LinkedHashMap<>();
		final List<Map<IProgramVar, Term>> vars_gevs = new ArrayList<>(mSettings.getNumberOfGevs());
		final List<Term> lambdas = new ArrayList<>(mSettings.getNumberOfGevs());
		for (final IProgramVar var : mLasso.getAllRankVars()) {
			final String name = SmtUtils.removeSmtQuoteCharacters(var.toString());
			vars_init.put(var, newConstant(PREFIX_INIT + name, sort));
			vars_honda.put(var, newConstant(PREFIX_HONDA + name, sort));
		}
		for (int i = 0; i < mSettings.getNumberOfGevs(); ++i) {
			final Map<IProgramVar, Term> vars_gev = new LinkedHashMap<>();
			for (final IProgramVar var : mLasso.getAllRankVars()) {
				final String name = SmtUtils.removeSmtQuoteCharacters(var.toString());
				vars_gev.put(var, newConstant(PREFIX_GE_VECTOR + name + i, sort));
			}
			vars_gevs.add(vars_gev);
			lambdas.add(newConstant(PREFIX_EVALUE + i, sort));
		}
		List<Term> nus;
		if (mSettings.getNumberOfGevs() > 0) {
			nus = new ArrayList<>(mSettings.getNumberOfGevs() - 1);
			for (int i = 0; i < mSettings.getNumberOfGevs() - 1; ++i) {
				nus.add(newConstant(PREFIX_NIL_POTENT + i, sort));
			}
		} else {
			nus = Collections.emptyList();
		}

		final Term constraints = generateConstraints(vars_init, vars_honda, vars_gevs, lambdas, nus);
		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(constraints)));
		mScript.assertTerm(constraints);

		// Check for satisfiability
		mIsSat = mScript.checkSat();
		if (mIsSat == LBool.SAT) {
			mArgument = extractArgument(vars_init, vars_honda, vars_gevs, lambdas, nus);
		} else if (mIsSat == LBool.UNKNOWN) {
			mScript.echo(new QuotedObject(ArgumentSynthesizer.s_SolverUnknownMessage));
		}
		return mIsSat;
	}

	/**
	 * Generate the constraints corresponding to the nontermination argument
	 *
	 * @param vars_init
	 *            assignment before the stem (z)
	 * @param vars_honda
	 *            assignment after the stem (x)
	 * @param vars_gevs
	 *            variables for the generalized eigenvectors (y_i)
	 * @param lambdas
	 *            variables for the eigenvalues
	 * @param nus
	 *            variables for the nilpotent components
	 * @return the constraints
	 */
	public Term generateConstraints(final Map<IProgramVar, Term> vars_init, final Map<IProgramVar, Term> vars_honda,
			final List<Map<IProgramVar, Term>> vars_gevs, final List<Term> lambdas, final List<Term> nus) {
		mSettings.checkSanity();
		assert mSettings.getNumberOfGevs() >= 0;
		assert vars_gevs.size() == mSettings.getNumberOfGevs();
		assert lambdas.size() == mSettings.getNumberOfGevs();
		int numvars;
		if (vars_gevs.isEmpty()) {
			numvars = 0;
		} else {
			numvars = vars_gevs.get(0).size();
		}
		assert numvars >= 0;

		final Collection<IProgramVar> rankVars = mLasso.getAllRankVars();

		Term zero; // = 0
		Term one; // = 1
		if (!mIntegerMode) {
			zero = mScript.decimal("0");
			one = mScript.decimal("1");
		} else {
			zero = mScript.numeral("0");
			one = mScript.numeral("1");
		}

		List<Term> lambda_guesses; // possible guesses for lambda if we are generating linear constraints
		List<Term> nu_guesses; // possible values for nus
		if (mAnalysisType == AnalysisType.NONLINEAR) {
			// Use a variable for lambda
			lambda_guesses = Collections.singletonList(null);
			nu_guesses = Collections.singletonList(null);
		} else {
			final List<Term> l = new ArrayList<>();
			l.add(zero);
			l.add(one);
			nu_guesses = Collections.unmodifiableList(l);

			if (mAnalysisType == AnalysisType.LINEAR) {
				// Just use lambda = 1
				lambda_guesses = Collections.singletonList(one);
			} else if (mAnalysisType == AnalysisType.LINEAR_WITH_GUESSES) {
				// Use a list of guesses for lambda
				final Rational[] eigenvalues = mLasso.guessEigenvalues(false);
				lambda_guesses = new ArrayList<>(eigenvalues.length);
				for (int i = 0; i < eigenvalues.length; ++i) {
					assert !eigenvalues[i].isNegative();
					if (mIntegerMode && !eigenvalues[i].isIntegral()) {
						continue; // ignore non-integral guesses
					}
					lambda_guesses.add(eigenvalues[i].toTerm(mSort));
				}
			} else {
				assert false; // unreachable branch
				lambda_guesses = Collections.emptyList();
			}
		}

		Term t1, t2, t3; // Three parts of the constraints

		// t1: A_stem * (z, x) <= b_stem
		t1 = mScript.term("true");
		if (!mLasso.getStem().isTrue()) {
			final LinearTransition stem = mLasso.getStem();
			final List<Term> disjunction = new ArrayList<>(stem.getNumPolyhedra());
			for (final List<LinearInequality> polyhedron : stem.getPolyhedra()) {
				disjunction.add(generateConstraint(stem, polyhedron, vars_init, vars_honda, false));
			}
			t1 = SmtUtils.or(mScript, disjunction.toArray(new Term[disjunction.size()]));
		}

		// vars_end + vars_gevs
		final Map<IProgramVar, Term> vars_end_plus_gevs = new LinkedHashMap<>();
		vars_end_plus_gevs.putAll(vars_honda);
		for (final IProgramVar rkVar : rankVars) {
			final Term[] summands = new Term[mSettings.getNumberOfGevs() + 1];
			summands[0] = vars_honda.get(rkVar);
			for (int i = 0; i < mSettings.getNumberOfGevs(); ++i) {
				summands[i + 1] = vars_gevs.get(i).get(rkVar);
			}
			final Term sum;
			if (summands.length == 1) {
				sum = summands[0];
			} else {
				sum = mScript.term("+", summands);
			}
			vars_end_plus_gevs.put(rkVar, sum);
		}

		// vars_gev[i] * lambda_guesses + nu_i * vars_gev[i+1] for each i
		final List<List<Map<IProgramVar, Term>>> vars_gevs_next = new ArrayList<>(mSettings.getNumberOfGevs());
		for (int i = 0; i < mSettings.getNumberOfGevs(); ++i) {
			final List<Map<IProgramVar, Term>> vars_gevs_next_i = new ArrayList<>(lambda_guesses.size());
			vars_gevs_next.add(vars_gevs_next_i);
			for (int j = 0; j < lambda_guesses.size(); ++j) {
				for (int k = 0; k < nu_guesses.size(); ++k) {
					Term lambda_guess = lambda_guesses.get(j);
					if (lambda_guess == null) {
						lambda_guess = lambdas.get(i);
					}
					Term nu_guess = nu_guesses.get(k);
					if (nu_guess == null && i < mSettings.getNumberOfGevs() - 1) {
						nu_guess = nus.get(i);
					}

					final Map<IProgramVar, Term> gev_next = new LinkedHashMap<>();
					vars_gevs_next_i.add(gev_next);
					for (final IProgramVar rkVar : rankVars) {
						if (mSettings.isNilpotentComponents() && i < mSettings.getNumberOfGevs() - 1) {
							gev_next.put(rkVar,
									mScript.term("+", mScript.term("*", vars_gevs.get(i).get(rkVar), lambda_guess),
											mScript.term("*", vars_gevs.get(i + 1).get(rkVar), nu_guess)));
						} else {
							gev_next.put(rkVar, mScript.term("*", vars_gevs.get(i).get(rkVar), lambda_guess));
						}
					}
				}
			}
		}

		// t2: honda and rays
		{
			final LinearTransition loop = mLasso.getLoop();
			final List<Term> disjunction = new ArrayList<>(loop.getNumPolyhedra());
			for (final List<LinearInequality> polyhedron : loop.getPolyhedra()) {
				// A_loop * (x, x + y) <= b_loop
				final Term t_honda = generateConstraint(loop, polyhedron, vars_honda, vars_end_plus_gevs, false);

				// A_loop * (y, lambda * y) <= 0
				final Term[] conjuction = new Term[mSettings.getNumberOfGevs() + 1];
				for (int i = 0; i < mSettings.getNumberOfGevs(); ++i) {
					final Term[] inner_disjunction = new Term[lambda_guesses.size()];
					for (int j = 0; j < lambda_guesses.size(); ++j) {
						final Term lambda_guess = lambda_guesses.get(j);
						final Term t_gev = generateConstraint(loop, polyhedron, vars_gevs.get(i),
								vars_gevs_next.get(i).get(j), true);
						Term fix_lambda;
						if (lambda_guess == null) {
							fix_lambda = mScript.term("true");
						} else {
							fix_lambda = mScript.term("=", lambdas.get(i), lambda_guess);
						}
						inner_disjunction[j] = SmtUtils.and(mScript, t_gev, fix_lambda);
					}
					conjuction[i] = SmtUtils.or(mScript, inner_disjunction);
				}
				conjuction[mSettings.getNumberOfGevs()] = t_honda;
				disjunction.add(SmtUtils.and(mScript, conjuction));
			}
			t2 = SmtUtils.or(mScript, disjunction.toArray(new Term[disjunction.size()]));
		}

		// t3: constraints on the lambdas and the nus
		{
			final List<Term> conjunction = new ArrayList<>(2 * mSettings.getNumberOfGevs());
			if (mSettings.isNilpotentComponents()) {
				// nu_i = 0 or nu_i = 1
				for (int i = 0; i < mSettings.getNumberOfGevs() - 1; ++i) {
					final Term nu = nus.get(i);
					conjunction.add(SmtUtils.or(mScript, mScript.term("=", nu, zero), mScript.term("=", nu, one)));
				}
			} else {
				// nu_i = 0
				for (int i = 0; i < mSettings.getNumberOfGevs() - 1; ++i) {
					final Term nu = nus.get(i);
					conjunction.add(mScript.term("=", nu, zero));
				}
			}
			if (mSettings.isAllowBounded()) {
				// lambda_i >= 0
				for (int i = 0; i < mSettings.getNumberOfGevs(); ++i) {
					conjunction.add(mScript.term(">=", lambdas.get(i), zero));
				}
			} else {
				// lambda >= 1 and any vars_gev != 0;
				final List<Term> disjunction = new ArrayList<>(mSettings.getNumberOfGevs() * numvars);
				for (int i = 0; i < mSettings.getNumberOfGevs(); ++i) {
					for (final Term t : vars_gevs.get(i).values()) {
						disjunction.add(mScript.term("<>", t, zero));
					}
					conjunction.add(mScript.term(">=", lambdas.get(i), one));
				}
				conjunction.add(SmtUtils.or(mScript, disjunction.toArray(new Term[disjunction.size()])));
			}
			t3 = SmtUtils.and(mScript, conjunction.toArray(new Term[conjunction.size()]));
		}

		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t1)));
		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t2)));
		mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t3)));
		return mScript.term("and", t1, t2, t3);
	}

	private Term generateConstraint(final LinearTransition transition, final List<LinearInequality> polyhedron,
			final Map<IProgramVar, Term> varsIn, final Map<IProgramVar, Term> varsOut, final boolean rays) {
		final Map<Term, Term> auxVars = new LinkedHashMap<>();
		final List<Term> conjunction = new ArrayList<>(polyhedron.size());
		for (final LinearInequality ieq : polyhedron) {
			final List<Term> summands = new ArrayList<>();
			final Collection<Term> added_vars = new LinkedHashSet<>();

			// outVars
			for (final Map.Entry<IProgramVar, TermVariable> entry : transition.getOutVars().entrySet()) {
				if (!varsOut.containsKey(entry.getKey())) {
					continue;
				}
				final AffineTerm a = ieq.getCoefficient(entry.getValue());
				summands.add(mScript.term("*", varsOut.get(entry.getKey()),
						mIntegerMode ? a.asIntTerm(mScript) : a.asRealTerm(mScript)));
				added_vars.add(entry.getValue());
			}

			// inVars
			for (final Map.Entry<IProgramVar, TermVariable> entry : transition.getInVars().entrySet()) {
				if (added_vars.contains(entry.getValue())) {
					// the transition implicitly requires that
					// entry.getKey() is constant
					conjunction.add(mScript.term("=", varsIn.get(entry.getKey()), varsOut.get(entry.getKey())));
					continue;
				}
				final AffineTerm a = ieq.getCoefficient(entry.getValue());
				summands.add(mScript.term("*", varsIn.get(entry.getKey()),
						mIntegerMode ? a.asIntTerm(mScript) : a.asRealTerm(mScript)));
				added_vars.add(entry.getValue());
			}

			// tmpVars
			final Set<Term> all_vars = new LinkedHashSet<>(ieq.getVariables());
			all_vars.removeAll(added_vars);
			for (final Term var : all_vars) {
				Term v;
				if (auxVars.containsKey(var)) {
					v = auxVars.get(var);
				} else {
					v = newConstant(PREFIX_AUX + sAuxCounter,
							mIntegerMode ? SmtSortUtils.INT_SORT : SmtSortUtils.REAL_SORT);
					auxVars.put(var, v);
				}
				final AffineTerm a = ieq.getCoefficient(var);
				summands.add(mScript.term("*", v, mIntegerMode ? a.asIntTerm(mScript) : a.asRealTerm(mScript)));
				++sAuxCounter;
			}
			if (!rays) {
				final AffineTerm a = ieq.getConstant();
				summands.add(mIntegerMode ? a.asIntTerm(mScript) : a.asRealTerm(mScript));
			}
			conjunction.add(mScript.term(rays ? ">=" : ieq.getInequalitySymbol(),
					SmtUtils.sum(mScript, mSort, summands.toArray(new Term[summands.size()])),
					mIntegerMode ? SmtUtils.constructIntValue(mScript, BigInteger.ZERO) : mScript.decimal("0")));
		}
		return SmtUtils.and(mScript, conjunction.toArray(new Term[conjunction.size()]));
	}

	/**
	 * Extract a program state from the SMT script's model
	 *
	 * @param vars
	 *            a map from the program variables to corresponding SMT variables
	 * @return the program state as a map from program variables to rational numbers
	 */
	private Map<IProgramVar, Rational> extractState(final Map<IProgramVar, Term> vars)
			throws SMTLIBException, UnsupportedOperationException, TermException {
		if (vars.isEmpty()) {
			return Collections.emptyMap();
		}
		final Map<Term, Rational> val = ModelExtractionUtils.getValuation(mScript, vars.values());
		// Concatenate vars and val
		final Map<IProgramVar, Rational> state = new LinkedHashMap<>();
		for (final Map.Entry<IProgramVar, Term> entry : vars.entrySet()) {
			assert (val.containsKey(entry.getValue()));
			state.put(entry.getKey(), val.get(entry.getValue()));
		}
		return state;
	}

	/**
	 * Extract the non-termination argument from a satisfiable script
	 *
	 * @return
	 * @throws SMTLIBException
	 */
	private GeometricNonTerminationArgument extractArgument(final Map<IProgramVar, Term> vars_init,
			final Map<IProgramVar, Term> vars_honda, final List<Map<IProgramVar, Term>> vars_gevs,
			final List<Term> var_lambdas, final List<Term> var_nus) {
		// assert mscript.checkSat() == LBool.SAT;

		try {
			final Map<IProgramVar, Rational> state0 = extractState(vars_init);
			final Map<IProgramVar, Rational> state1 = extractState(vars_honda);
			final List<Map<IProgramVar, Rational>> gevs = new ArrayList<>(mSettings.getNumberOfGevs());
			final Map<Term, Term> lambda_val;
			if (!var_lambdas.isEmpty()) {
				lambda_val = mScript.getValue(var_lambdas.toArray(new Term[var_lambdas.size()]));
			} else {
				lambda_val = Collections.emptyMap();
			}
			final Map<Term, Term> nu_val;
			if (!var_nus.isEmpty()) {
				nu_val = mScript.getValue(var_nus.toArray(new Term[var_nus.size()]));
			} else {
				nu_val = Collections.emptyMap();
			}
			final List<Rational> lambdas = new ArrayList<>(mSettings.getNumberOfGevs());
			final List<Rational> nus = new ArrayList<>();
			for (int i = 0; i < mSettings.getNumberOfGevs(); ++i) {
				gevs.add(extractState(vars_gevs.get(i)));
				lambdas.add(ModelExtractionUtils.const2Rational(lambda_val.get(var_lambdas.get(i))));
				if (i < mSettings.getNumberOfGevs() - 1) {
					nus.add(ModelExtractionUtils.const2Rational(nu_val.get(var_nus.get(i))));
				}
			}
			final boolean has_stem = !mLasso.getStem().isTrue();
			return new GeometricNonTerminationArgument(has_stem ? state0 : state1, state1, gevs, lambdas, nus);
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
		return mArgument;
	}

}
