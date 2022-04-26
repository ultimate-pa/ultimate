/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskFileIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.ContinueDirective;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.TermcompProofBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.InterpolationPreferenceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public abstract class AbstractBuchiCegarLoop<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>> {

	/**
	 * Result of CEGAR loop iteration
	 * <ul>
	 * <li>SAFE: there is no feasible trace to an error location
	 * <li>UNSAFE: there is a feasible trace to an error location (the underlying program has at least one execution
	 * which violates its specification)
	 * <li>UNKNOWN: we found a trace for which we could not decide feasibility or we found an infeasible trace but were
	 * not able to exclude it in abstraction refinement.
	 * <li>TIMEOUT:
	 */
	public enum Result {
		TERMINATING, TIMEOUT, UNKNOWN, NONTERMINATING
	}

	protected static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;
	protected static final XnfConversionTechnique XNF_CONVERSION_TECHNIQUE =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	protected final ILogger mLogger;

	/**
	 * Node of a recursive control flow graph which stores additional information about the
	 */
	protected final IIcfg<?> mIcfg;

	protected final CfgSmtToolkit mCsToolkitWithoutRankVars;
	protected final CfgSmtToolkit mCsToolkitWithRankVars;

	private final PredicateFactory mPredicateFactory;

	protected final BinaryStatePredicateManager mBinaryStatePredicateManager;

	/**
	 * Intermediate layer to encapsulate preferences.
	 */
	protected final TAPreferences mPref;

	/**
	 * Current Iteration of this CEGAR loop.
	 */
	protected int mIteration;

	/**
	 * Accepting run of the abstraction obtained in this iteration.
	 */
	protected NestedLassoRun<L, IPredicate> mCounterexample;

	/**
	 * Abstraction of this iteration. The language of mAbstraction is a set of traces which is
	 * <ul>
	 * <li>a superset of the feasible program traces.
	 * <li>a subset of the traces which respect the control flow of of the program.
	 */
	protected A mAbstraction;

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected NestedWordAutomaton<L, IPredicate> mInterpolAutomaton;

	protected A mArtifactAutomaton;

	protected final PredicateFactoryForInterpolantAutomata mDefaultStateFactory;

	protected final BuchiAutomizerModuleDecompositionBenchmark mMDBenchmark;

	protected final BuchiCegarLoopBenchmarkGenerator mBenchmarkGenerator;

	/**
	 * Construct a termination proof in the form that is required for the Termination Competition.
	 * http://termination-portal.org/wiki/Termination_Competition This proof is finally print in the console output and
	 * can be huge.
	 */
	protected final boolean mConstructTermcompProof;
	protected final TermcompProofBenchmark mTermcompProofBenchmark;

	protected final InterpolationTechnique mInterpolation;

	private final Minimization mAutomataMinimizationAfterFeasbilityBasedRefinement;
	private final Minimization mAutomataMinimizationAfterRankBasedRefinement;

	private NonTerminationArgument mNonterminationArgument;

	protected final IUltimateServiceProvider mServices;

	private ToolchainCanceledException mToolchainCancelledException;
	private final RankVarConstructor mRankVarConstructor;

	private final StrategyFactory<L> mRefinementStrategyFactory;
	private final TaskIdentifier mTaskIdentifier;

	private final Class<L> mTransitionClazz;

	public AbstractBuchiCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz, final A initialAbstraction,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		assert services != null;
		mIcfg = icfg;
		mTransitionClazz = transitionClazz;
		// TODO: TaskIdentifier should probably be provided by caller
		mTaskIdentifier = new SubtaskFileIdentifier(null, mIcfg.getIdentifier());
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mMDBenchmark = new BuchiAutomizerModuleDecompositionBenchmark(mServices.getBacktranslationService());
		mPredicateFactory = predicateFactory;
		mRankVarConstructor = rankVarConstructor;
		mCsToolkitWithoutRankVars = mIcfg.getCfgSmtToolkit();
		mCsToolkitWithRankVars = mRankVarConstructor.getCsToolkitWithRankVariables();
		mBinaryStatePredicateManager = new BinaryStatePredicateManager(mCsToolkitWithRankVars, predicateFactory,
				mRankVarConstructor.getUnseededVariable(), mRankVarConstructor.getOldRankVariables(), mServices,
				SIMPLIFICATION_TECHNIQUE);
		mBenchmarkGenerator = benchmarkGenerator;
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.OverallTime.toString());

		mPref = taPrefs;
		mDefaultStateFactory = new PredicateFactoryForInterpolantAutomata(mCsToolkitWithRankVars.getManagedScript(),
				predicateFactory, mPref.computeHoareAnnotation());

		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		mAutomataMinimizationAfterFeasbilityBasedRefinement = baPref.getEnum(
				BuchiAutomizerPreferenceInitializer.LABEL_AUTOMATA_MINIMIZATION_AFTER_FEASIBILITY_BASED_REFINEMENT,
				Minimization.class);
		mAutomataMinimizationAfterRankBasedRefinement = baPref.getEnum(
				BuchiAutomizerPreferenceInitializer.LABEL_AUTOMATA_MINIMIZATION_AFTER_RANK_BASED_REFINEMENT,
				Minimization.class);
		mInterpolation = baPref.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS,
				InterpolationTechnique.class);

		InterpolationPreferenceChecker.check(Activator.PLUGIN_NAME, mInterpolation, mServices);
		mConstructTermcompProof = baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_CONSTRUCT_TERMCOMP_PROOF);
		mTermcompProofBenchmark = mConstructTermcompProof ? new TermcompProofBenchmark(mServices) : null;

		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs =
				new TaCheckAndRefinementPreferences<>(mServices, mPref, mInterpolation, SIMPLIFICATION_TECHNIQUE,
						XNF_CONVERSION_TECHNIQUE, mCsToolkitWithoutRankVars, mPredicateFactory, mIcfg);
		mRefinementStrategyFactory = new StrategyFactory<>(mLogger, mPref, taCheckAndRefinementPrefs, mIcfg,
				mPredicateFactory, mDefaultStateFactory, mTransitionClazz);
		mAbstraction = initialAbstraction;
	}

	public NestedLassoRun<L, IPredicate> getCounterexample() {
		return mCounterexample;
	}

	public final Result runCegarLoop() throws IOException {
		mLogger.info("Interprodecural is " + mPref.interprocedural());
		mLogger.info("Hoare is " + mPref.computeHoareAnnotation());
		mLogger.info("Compute interpolants for " + mInterpolation);
		mLogger.info("Backedges is " + mPref.interpolantAutomaton());
		mLogger.info("Determinization is " + mPref.interpolantAutomatonEnhancement());
		mLogger.info("Difference is " + mPref.differenceSenwa());
		mLogger.info("Minimize is " + mPref.getMinimization());

		mIteration = 0;
		final String name = getClass().getName();
		mLogger.info("======== Iteration " + mIteration + "==of CEGAR loop == " + name + "========");

		if (mIteration <= mPref.watchIteration()
				&& (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.RCFG)) {
			mArtifactAutomaton = mAbstraction;
		}
		if (mPref.dumpAutomata()) {
			final String filename = mIcfg.getIdentifier() + "_" + name + "Abstraction" + mIteration;
			BuchiAutomizerUtils.writeAutomatonToFile(mServices, mAbstraction, mPref.dumpPath(), filename,
					mPref.getAutomataFormat(), "");
		}
		boolean initalAbstractionCorrect;
		try {
			initalAbstractionCorrect = isAbstractionEmpty();
		} catch (final AutomataLibraryException e1) {
			mLogger.warn("Verification cancelled");
			mMDBenchmark.reportRemainderModule(mAbstraction.size(), false);
			mToolchainCancelledException = new ToolchainCanceledException(e1.getClassOfThrower());
			return Result.TIMEOUT;
		}
		if (initalAbstractionCorrect) {
			mMDBenchmark.reportNoRemainderModule();
			return Result.TERMINATING;
		}

		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			mLogger.info("======== Iteration " + mIteration + "============");
			mBenchmarkGenerator.announceNextIteration();
			boolean abstractionCorrect;
			try {
				abstractionCorrect = isAbstractionEmpty();
			} catch (final AutomataLibraryException e1) {
				mLogger.warn("Verification cancelled");
				reportRemainderModule(false);
				mToolchainCancelledException = new ToolchainCanceledException(e1.getClassOfThrower());
				return Result.TIMEOUT;
			}
			if (abstractionCorrect) {
				mMDBenchmark.reportNoRemainderModule();
				if (mConstructTermcompProof) {
					mTermcompProofBenchmark.reportNoRemainderModule();
				}
				return Result.TERMINATING;
			}

			LassoCheck<L> lassoCheck;
			try {
				final TaskIdentifier taskIdentifier = new SubtaskIterationIdentifier(mTaskIdentifier, mIteration);
				mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.LASSO_ANALYSIS_TIME);
				lassoCheck = new LassoCheck<>(mCsToolkitWithoutRankVars, mPredicateFactory,
						mIcfg.getCfgSmtToolkit().getSmtFunctionsAndAxioms(), mBinaryStatePredicateManager,
						mCounterexample, generateLassoCheckIdentifier(), mServices, SIMPLIFICATION_TECHNIQUE,
						XNF_CONVERSION_TECHNIQUE, mRefinementStrategyFactory, mAbstraction, taskIdentifier,
						mBenchmarkGenerator);
				if (lassoCheck.getLassoCheckResult().getContinueDirective() == ContinueDirective.REPORT_UNKNOWN) {
					// if result was unknown, then try again but this time add one
					// iteration of the loop to the stem.
					// This allows us to verify Vincent's coolant examples
					final TaskIdentifier unwindingTaskIdentifier =
							new SubtaskAdditionalLoopUnwinding(taskIdentifier, 1);
					mLogger.info("Result of lasso check was UNKNOWN. I will concatenate loop to stem and try again.");
					final NestedRun<L, IPredicate> newStem =
							mCounterexample.getStem().concatenate(mCounterexample.getLoop());
					mCounterexample = new NestedLassoRun<>(newStem, mCounterexample.getLoop());
					lassoCheck = new LassoCheck<>(mCsToolkitWithoutRankVars, mPredicateFactory,
							mIcfg.getCfgSmtToolkit().getSmtFunctionsAndAxioms(), mBinaryStatePredicateManager,
							mCounterexample, generateLassoCheckIdentifier(), mServices, SIMPLIFICATION_TECHNIQUE,
							XNF_CONVERSION_TECHNIQUE, mRefinementStrategyFactory, mAbstraction, unwindingTaskIdentifier,
							mBenchmarkGenerator);
				}
			} catch (final ToolchainCanceledException e) {
				final int traceHistogramMaxStem =
						new HistogramOfIterable<>(mCounterexample.getStem().getWord()).getMax();
				final int traceHistogramMaxLoop =
						new HistogramOfIterable<>(mCounterexample.getLoop().getWord()).getMax();
				final String taskDescription =
						"analyzing lasso (" + "stem: length " + mCounterexample.getStem().getLength() + " TraceHistMax "
								+ traceHistogramMaxStem + " " + "loop: length " + mCounterexample.getLoop().getLength()
								+ " TraceHistMax " + traceHistogramMaxLoop + ")";
				e.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
				mToolchainCancelledException = e;
				return Result.TIMEOUT;
			} finally {
				mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.LASSO_ANALYSIS_TIME);
			}

			final ContinueDirective cd = lassoCheck.getLassoCheckResult().getContinueDirective();
			mBenchmarkGenerator.reportLassoAnalysis(lassoCheck);
			try {
				switch (cd) {
				case REFINE_BOTH:
					refineBuchiInternal(lassoCheck);
					refineFiniteInternal(lassoCheck);
					break;
				case REFINE_FINITE:
					refineFiniteInternal(lassoCheck);
					break;
				case REFINE_BUCHI:
					refineBuchiInternal(lassoCheck);
					break;
				case REPORT_UNKNOWN:
					reportRemainderModule(false);
					return Result.UNKNOWN;
				case REPORT_NONTERMINATION:
					if (getOverapproximations().isEmpty()) {
						mNonterminationArgument = lassoCheck.getNonTerminationArgument();
						reportRemainderModule(true);
						return Result.NONTERMINATING;
					}
					reportRemainderModule(false);
					return Result.UNKNOWN;
				default:
					throw new AssertionError("impossible case");
				}
				mLogger.info("Abstraction has " + mAbstraction.sizeInformation());
				if (mIteration <= mPref.watchIteration() && mPref.artifact() == Artifact.ABSTRACTION) {
					mArtifactAutomaton = mAbstraction;
				}

				if (mPref.dumpAutomata()) {
					final String filename = mIcfg.getIdentifier() + "_" + name + "Abstraction" + mIteration;
					BuchiAutomizerUtils.writeAutomatonToFile(mServices, mAbstraction, mPref.dumpPath(), filename,
							mPref.getAutomataFormat(), "");
				}

			} catch (final AutomataOperationCanceledException e) {
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(), "performing iteration " + mIteration);
				mToolchainCancelledException = new ToolchainCanceledException(e, rti);
				return Result.TIMEOUT;
			} catch (final ToolchainCanceledException e) {
				mToolchainCancelledException = e;
				return Result.TIMEOUT;
			}
			mInterpolAutomaton = null;
		}
		return Result.TIMEOUT;
	}

	private void refineFiniteInternal(final LassoCheck<L> lassoCheck) throws AutomataOperationCanceledException {
		refineFinite(lassoCheck);
		reduceAbstractionSize(mAutomataMinimizationAfterFeasbilityBasedRefinement);
	}

	private void refineBuchiInternal(final LassoCheck<L> lassoCheck) throws AutomataOperationCanceledException {
		final BinaryStatePredicateManager bspm = lassoCheck.getBinaryStatePredicateManager();
		final ISLPredicate hondaISLP = (ISLPredicate) mCounterexample.getLoop().getStateAtPosition(0);
		final IcfgLocation hondaPP = hondaISLP.getProgramPoint();
		final TerminationArgumentResult<IIcfgElement, Term> tar =
				constructTAResult(bspm.getTerminationArgument(), hondaPP);
		mMDBenchmark.reportRankingFunction(mIteration, tar);

		refineBuchi(lassoCheck);
		mBinaryStatePredicateManager.clearPredicates();
		reduceAbstractionSize(mAutomataMinimizationAfterRankBasedRefinement);
	}

	private void reportRemainderModule(final boolean nonterminationKnown) {
		mMDBenchmark.reportRemainderModule(mAbstraction.size(), nonterminationKnown);
		if (mConstructTermcompProof) {
			mTermcompProofBenchmark.reportRemainderModule(nonterminationKnown);
		}
	}

	public Map<String, ILocation> getOverapproximations() {
		final NestedWord<L> stem = mCounterexample.getStem().getWord();
		final NestedWord<L> loop = mCounterexample.getLoop().getWord();
		final Map<String, ILocation> overapproximations = new HashMap<>();
		overapproximations.putAll(Overapprox.getOverapproximations(stem.asList()));
		overapproximations.putAll(Overapprox.getOverapproximations(loop.asList()));
		return overapproximations;
	}

	/**
	 * @param automataMinimization
	 * @throws AutomataOperationCanceledException
	 * @throws AutomataLibraryException
	 * @throws AssertionError
	 */
	protected abstract void reduceAbstractionSize(final Minimization automataMinimization)
			throws AutomataOperationCanceledException;

	protected abstract void refineBuchi(final LassoCheck<L> lassoCheck) throws AutomataOperationCanceledException;

	protected abstract boolean isAbstractionEmpty() throws AutomataLibraryException;

	/**
	 * Do a refinement (i.e., replace mAbstraction by a new difference) for the case where we detected that a finite
	 * prefix of the lasso-shaped counterexample is infeasible. In this case the module (i.e., the subtrahend of the
	 * difference) will be a weak Büchi automaton (Büchi automaton where set of final states is a trap). In fact, the
	 * module will have only a single accepting state that is labeled with "false" and that has a self-loop for every
	 * letter.
	 *
	 * In this case we construct the module with the same algorithm that we use in our safety analysis (there the
	 * Floyd-Hoare automata also have a single accepting state that is labeled with "false" and that has a self-loop for
	 * every letter). "Coincidentally" is holds that for these kind of automata the powerset-based complementation of
	 * finite automata is also sound for Büchi automata, hence we use a difference operation that is based on this
	 * rather inexpensive complementation algorithm.
	 *
	 */
	protected abstract void refineFinite(final LassoCheck<L> lassoCheck) throws AutomataOperationCanceledException;

	private TerminationArgumentResult<IIcfgElement, Term>
			constructTAResult(final TerminationArgument terminationArgument, final IcfgLocation honda) {
		final RankingFunction rf = terminationArgument.getRankingFunction();
		final Term[] supportingInvariants = terminationArgument.getSupportingInvariants().stream()
				.map(si -> si.asTerm(mCsToolkitWithRankVars.getManagedScript().getScript())).toArray(Term[]::new);
		return new TerminationArgumentResult<>(honda, Activator.PLUGIN_NAME,
				rf.asLexTerm(mCsToolkitWithRankVars.getManagedScript().getScript()), rf.getName(), supportingInvariants,
				mServices.getBacktranslationService(), Term.class);
	}

	public ToolchainCanceledException getToolchainCancelledException() {
		return mToolchainCancelledException;
	}

	public NonTerminationArgument getNonTerminationArgument() {
		return mNonterminationArgument;
	}

	public BuchiAutomizerModuleDecompositionBenchmark getMDBenchmark() {
		return mMDBenchmark;
	}

	public TermcompProofBenchmark getTermcompProofBenchmark() {
		return mTermcompProofBenchmark;
	}

	/**
	 * Returns an Identifier that describes a lasso analysis. Right now, this is the Filename (without path prefix) of
	 * analyzed file together with the number of the current iteration.
	 *
	 */
	private String generateLassoCheckIdentifier() {
		return mIcfg.getIdentifier() + "_Iteration" + mIteration;
	}

	private static class SubtaskAdditionalLoopUnwinding extends TaskIdentifier {
		private final int mAdditionaUnwindings;

		public SubtaskAdditionalLoopUnwinding(final TaskIdentifier parentTaskIdentifier,
				final int additionaUnwindings) {
			super(parentTaskIdentifier);
			mAdditionaUnwindings = additionaUnwindings;
		}

		@Override
		protected String getSubtaskIdentifier() {
			return mAdditionaUnwindings + "additionalUnwindings";
		}

	}

}
