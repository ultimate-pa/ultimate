/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.ArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.ILassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.Lasso;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality.PossibleMotzkinCoefficients;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.ModelExtractionUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.RankingTemplate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This is the synthesizer that generates ranking functions.
 *
 * @author Jan Leike
 */
public class TerminationArgumentSynthesizer extends ArgumentSynthesizer {
	/**
	 * The (local) settings for termination analysis
	 */
	private TerminationAnalysisSettings mSettings;

	/**
	 * The template to be used
	 */
	private final RankingTemplate mTemplate;

	/**
	 * List of supporting invariant generators used by the last synthesize() call
	 */
	private final Collection<SupportingInvariantGenerator> msi_generators;

	/**
	 * Number of Motzkin's Theorem applications used by the last synthesize() call
	 */
	private int mnum_motzkin = 0;

	// Objects resulting from the synthesis process
	private RankingFunction mranking_function = null;
	private Collection<SupportingInvariant> mSupportingInvariants = null;

	/**
	 * Set of terms in which RewriteArrays has put additional supporting invariants
	 */
	private final Set<Term> mArrayIndexSupportingInvariants;

	/**
	 * Constructor for the termination argument function synthesizer.
	 *
	 * @param lasso
	 *            the lasso program
	 * @param template
	 *            the ranking function template to be used in the analysis
	 * @param preferences
	 *            arguments to the synthesis process
	 * @param settings
	 *            (local) settings for termination analysis
	 * @param arrayIndexSupportingInvariants
	 *            supporting invariants that were discovered during preprocessing
	 * @param services
	 * @throws IOException
	 */
	public TerminationArgumentSynthesizer(final Lasso lasso, final RankingTemplate template,
			final ILassoRankerPreferences preferences, final TerminationAnalysisSettings settings,
			final Set<Term> arrayIndexSupportingInvariants, final IUltimateServiceProvider services)
			throws IOException {
		super(lasso, preferences, template.getName() + "Template", services);
		mSettings = settings;
		mLogger.info("Termination Analysis Settings:\n" + settings.toString());
		assert !mSettings.getAnalysis().isDisabled();
		if (mSettings.getNumStrictInvariants() == 0 && mSettings.getNumNonStrictInvariants() == 0) {
			mLogger.info("Generation of supporting invariants is disabled.");
		}

		// Set logic
		if (mSettings.getAnalysis().isLinear()) {
			mScript.setLogic(Logics.QF_LRA);
		} else {
			mScript.setLogic(Logics.QF_NRA);
		}
		if (mSettings.getAnalysis() == AnalysisType.LINEAR && !settings.isNonDecreasingInvariants()) {
			mLogger.warn("Termination analysis type is 'Linear', " + "hence invariants must be non-decreasing!");
		}

		// Set other fields
		mTemplate = template;
		msi_generators = new ArrayList<>();
		mSupportingInvariants = new ArrayList<>();
		mArrayIndexSupportingInvariants = arrayIndexSupportingInvariants;
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
		final String solverId = "TerminationArgumentSynthesis solver ";
		return SolverBuilder.buildAndInitializeSolver(mServices, solverMode, settings, false, false, null, solverId);
	}

	/**
	 * @return RankVar's that are relevant for supporting invariants
	 */
	public Collection<IProgramVar> getSIVars() {
		/*
		 * Variables that occur as outVars of the stem but are not read by the loop (i.e., do not occur as inVar of the
		 * loop) are not relevant for supporting invariants.
		 */
		final Collection<IProgramVar> result = new LinkedHashSet<>(mLasso.getStem().getOutVars().keySet());
		result.retainAll(mLasso.getLoop().getInVars().keySet());
		return result;
	}

	/**
	 * @return RankVar's that are relevant for ranking functions
	 */
	public Collection<IProgramVar> getRankVars() {
		final Collection<IProgramVar> result = new LinkedHashSet<>(mLasso.getLoop().getOutVars().keySet());
		result.retainAll(mLasso.getLoop().getInVars().keySet());
		return result;
	}

	/**
	 * Use the ranking template to build the constraints whose solution gives the termination argument
	 *
	 * @param template
	 *            the ranking function template
	 * @param si_generators
	 *            Output container for the used SI generators
	 * @return List of all conjuncts of the constraints
	 */
	private Collection<Term> buildConstraints(final LinearTransition stem, final LinearTransition loop,
			final RankingTemplate template, final Collection<SupportingInvariantGenerator> si_generators) {

		final List<Term> conj = new ArrayList<>(); // List of constraints

		final Collection<IProgramVar> siVars = getSIVars();
		final List<List<LinearInequality>> templateConstraints =
				template.getConstraints(loop.getInVars(), loop.getOutVars());
		final List<String> annotations = template.getAnnotations();
		assert annotations.size() == templateConstraints.size();

		mLogger.info(stem.getNumPolyhedra() + " stem disjuncts");
		mLogger.info(loop.getNumPolyhedra() + " loop disjuncts");
		mLogger.info(templateConstraints.size() + " template conjuncts.");

		// Negate template inequalities
		{
			final Set<LinearInequality> negated = new HashSet<>();
			/*
			 * The same linear inequality may occur multiple times in the constraints if we use a composed template.
			 * That's why we have to make sure that we are not negating the same linear inequality twice.
			 *
			 * Guess how much debugging it took me to find this error... :/
			 */
			for (final List<LinearInequality> templateDisj : templateConstraints) {
				for (final LinearInequality li : templateDisj) {
					if (!negated.contains(li)) {
						li.negate();
						negated.add(li);
					}
				}
			}
		}

		// Get guesses for loop eigenvalues as possible Motzkin coefficients
		Rational[] eigenvalue_guesses;
		if (mSettings.getAnalysis().wantsGuesses()) {
			eigenvalue_guesses = mLasso.guessEigenvalues(false);
			assert eigenvalue_guesses.length >= 2;
		} else {
			eigenvalue_guesses = new Rational[0];
		}

		// loop(x, x') /\ si(x) -> template(x, x')
		// Iterate over the loop conjunctions and template disjunctions
		int j = 0;
		for (final List<LinearInequality> loopConj : loop.getPolyhedra()) {
			++j;
			for (int m = 0; m < templateConstraints.size(); ++m) {
				final MotzkinTransformation motzkin = new MotzkinTransformation(mServices, mScript,
						mSettings.getAnalysis(), mPreferences.isAnnotateTerms());
				motzkin.mAnnotation = annotations.get(m) + " " + j;
				motzkin.addInequalities(loopConj);
				motzkin.addInequalities(templateConstraints.get(m));

				// Add supporting invariants
				assert (mSettings.getNumStrictInvariants() >= 0);
				for (int i = 0; i < mSettings.getNumStrictInvariants(); ++i) {
					final SupportingInvariantGenerator sig = new SupportingInvariantGenerator(mScript, siVars, true);
					si_generators.add(sig);
					motzkin.addInequality(sig.generate(loop.getInVars()));
				}
				assert (mSettings.getNumNonStrictInvariants() >= 0);
				for (int i = 0; i < mSettings.getNumNonStrictInvariants(); ++i) {
					final SupportingInvariantGenerator sig = new SupportingInvariantGenerator(mScript, siVars, false);
					si_generators.add(sig);
					final LinearInequality li = sig.generate(loop.getInVars());
					li.mMotzkinCoefficient = PossibleMotzkinCoefficients.ONE;
					motzkin.addInequality(li);
				}
				mLogger.debug(motzkin);
				conj.add(motzkin.transform(eigenvalue_guesses));
			}
		}

		// Add constraints for the supporting invariants
		mLogger.debug("Adding the constraints for " + si_generators.size() + " supporting invariants.");
		int i = 0;
		for (final SupportingInvariantGenerator sig : si_generators) {
			++i;

			// stem(x0) -> si(x0)
			j = 0;
			for (final List<LinearInequality> stemConj : stem.getPolyhedra()) {
				++j;
				final MotzkinTransformation motzkin = new MotzkinTransformation(mServices, mScript,
						mSettings.getAnalysis(), mPreferences.isAnnotateTerms());
				motzkin.mAnnotation = "invariant " + i + " initiation " + j;
				motzkin.addInequalities(stemConj);
				final LinearInequality li = sig.generate(stem.getOutVars());
				li.negate();
				li.mMotzkinCoefficient = PossibleMotzkinCoefficients.ONE;
				motzkin.addInequality(li);
				conj.add(motzkin.transform(eigenvalue_guesses));
			}

			// si(x) /\ loop(x, x') -> si(x')
			j = 0;
			for (final List<LinearInequality> loopConj : loop.getPolyhedra()) {
				++j;
				final MotzkinTransformation motzkin = new MotzkinTransformation(mServices, mScript,
						mSettings.getAnalysis(), mPreferences.isAnnotateTerms());
				motzkin.mAnnotation = "invariant " + i + " consecution " + j;
				motzkin.addInequalities(loopConj);
				motzkin.addInequality(sig.generate(loop.getInVars())); // si(x)
				final LinearInequality li = sig.generate(loop.getOutVars()); // ~si(x')
				li.mMotzkinCoefficient =
						mSettings.isNonDecreasingInvariants() || mSettings.getAnalysis() == AnalysisType.LINEAR
								? PossibleMotzkinCoefficients.ZERO_AND_ONE
								: PossibleMotzkinCoefficients.ANYTHING;
				li.negate();
				motzkin.addInequality(li);
				conj.add(motzkin.transform(eigenvalue_guesses));
			}
		}
		return conj;
	}

	/**
	 * Ranking function generation for lasso programs
	 *
	 * This procedure is complete in the sense that if there is a linear ranking function that can be derived with a
	 * linear supporting invariant of the form si(x) >= 0, then it will be found by this procedure.
	 *
	 * Iff a ranking function is found, this method returns true and the resulting ranking function and supporting
	 * invariant can be retrieved using the methods getRankingFunction() and getSupportingInvariant().
	 *
	 * @param template
	 *            the ranking template to be used
	 * @return SAT if a termination argument was found, UNSAT if existence of a termination argument was refuted,
	 *         UNKNOWN if the solver was not able to decide existence of a termination argument
	 * @throws SMTLIBException
	 *             error with the SMT solver
	 * @throws TermException
	 *             if the supplied transitions contain non-affine update statements
	 * @throws IOException
	 */
	@Override
	protected LBool do_synthesis() throws SMTLIBException, TermException, IOException {
		mTemplate.init(this);
		if (mSettings.getAnalysis().isLinear() && mTemplate.getDegree() > 0) {
			mLogger.warn(
					"Using a linear SMT query and a templates of degree " + "> 0, hence this method is incomplete.");
		}
		final Collection<IProgramVar> rankVars = getRankVars();
		final Collection<IProgramVar> siVars = getSIVars();
		mLogger.info("Template has degree " + mTemplate.getDegree() + ".");
		mLogger.debug("Variables for ranking functions: " + rankVars);
		mLogger.debug("Variables for supporting invariants: " + siVars);

		LinearTransition stem = mLasso.getStem();
		final LinearTransition loop = mLasso.getLoop();

		/*
		 * // The following code makes examples like StemUnsat.bpl fail if (siVars.isEmpty()) { s_Logger.info(
		 * "There is no variables for invariants; " + "disabling supporting invariant generation.");
		 * mpreferences.numstrict_invariants = 0; mpreferences.numnon_strict_invariants = 0; }
		 */
		if (mLasso.getStem().isTrue()) {
			mLogger.info("There is no stem transition; " + "disabling supporting invariant generation.");
			mSettings = new TerminationAnalysisSettings(new ITerminationAnalysisSettings() {

				@Override
				public AnalysisType getAnalysis() {
					return mSettings.getAnalysis();
				}

				@Override
				public int getNumStrictInvariants() {
					return 0;
				}

				@Override
				public int getNumNonStrictInvariants() {
					return 0;
				}

				@Override
				public boolean isNonDecreasingInvariants() {
					return mSettings.isNonDecreasingInvariants();
				}

				@Override
				public boolean isSimplifyTerminationArgument() {
					return mSettings.isSimplifyTerminationArgument();
				}

				@Override
				public boolean isSimplifySupportingInvariants() {
					return mSettings.isSimplifySupportingInvariants();
				}

				@Override
				public boolean isOverapproximateStem() {
					return mSettings.isOverapproximateStem();
				}

			});
		} else if (mSettings.isOverapproximateStem()) {
			mLogger.info("Overapproximating stem...");
			final StemOverapproximator so = new StemOverapproximator(mPreferences, mServices);
			final int stematoms = stem.getNumInequalities();
			stem = so.overapproximate(stem);
			mLogger.info("Reduced " + stematoms + " stem atoms to " + stem.getNumInequalities() + ".");
		}

		// Assert all conjuncts generated from the template
		final Collection<Term> constraints = buildConstraints(stem, loop, mTemplate, msi_generators);
		mnum_motzkin = constraints.size();
		mLogger.info("We have " + getNumMotzkin() + " Motzkin's Theorem applications.");
		mLogger.info("A total of " + getNumSIs() + " supporting invariants were added.");
		for (final Term constraint : constraints) {
			mScript.assertTerm(constraint);
		}

		// Check for a model
		final LBool sat = mScript.checkSat();
		if (sat == LBool.SAT) {
			// Get all relevant variables
			final ArrayList<Term> coefficients = new ArrayList<>();
			coefficients.addAll(mTemplate.getCoefficients());
			for (final SupportingInvariantGenerator sig : msi_generators) {
				coefficients.addAll(sig.getCoefficients());
			}

			// Get valuation for the variables
			Map<Term, Rational> val;
			if (mSettings.isSimplifyTerminationArgument()) {
				mLogger.info("Found a termination argument, trying to simplify.");
				val = ModelExtractionUtils.getSimplifiedAssignment_TwoMode(mScript, coefficients, mLogger, mServices);
			} else {
				val = ModelExtractionUtils.getValuation(mScript, coefficients);
			}

			// Extract ranking function and supporting invariants
			mranking_function = mTemplate.extractRankingFunction(val);
			for (final SupportingInvariantGenerator sig : msi_generators) {
				mSupportingInvariants.add(sig.extractSupportingInvariant(val));
			}

			// Simplify supporting invariants
			if (mSettings.isSimplifySupportingInvariants()) {
				final SupportingInvariantSimplifier tas =
						new SupportingInvariantSimplifier(mPreferences, mServices);
				mLogger.info("Simplifying supporting invariants...");
				final int before = mSupportingInvariants.size();
				mSupportingInvariants = tas.simplify(mSupportingInvariants);
				mLogger.info("Removed " + (before - mSupportingInvariants.size())
						+ " redundant supporting invariants from a total of " + before + ".");
			}
		} else if (sat == LBool.UNKNOWN) {
			mScript.echo(new QuotedObject(ArgumentSynthesizer.s_SolverUnknownMessage));
			// Problem: If we use the following line we can receive the
			// following response which is not SMTLIB2 compliant.
			// (:reason-unknown canceled)
			// Object reason = mscript.getInfo(":reason-unknown");
			// TODO: discuss the above claim with Jürgen
		}
		return sat;
	}

	/**
	 * @return the number of supporting invariants used
	 */
	public int getNumSIs() {
		assert msi_generators != null;
		return msi_generators.size();
	}

	/**
	 * @return the number of Motzkin's Theorem applications
	 */
	public int getNumMotzkin() {
		return mnum_motzkin;
	}

	/**
	 * @return the synthesized TerminationArgument
	 */
	public TerminationArgument getArgument() {
		assert synthesisSuccessful();
		return new TerminationArgument(mranking_function, mSupportingInvariants, mArrayIndexSupportingInvariants);
	}

}
