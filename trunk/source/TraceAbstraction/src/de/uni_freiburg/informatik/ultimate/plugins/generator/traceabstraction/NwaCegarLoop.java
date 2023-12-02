/*
 * Copyright (C) 2013-2022 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty.SearchStrategy;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.AStarHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.IHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ProductNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.DangerInvariantResult;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier.ScoringMethod;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.cfg2automaton.Cfg2Automaton;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare.HoareAnnotationComposer;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare.HoareAnnotationExtractor;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare.HoareAnnotationFragments;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.proofs.IUpdateOnDifference;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.proofs.IUpdateOnMinimization;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram.PathProgramConstructionResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.DangerInvariantGuesser;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.CounterexampleSearchStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

/**
 * Subclass of BasicCegarLoop for safety checking based on nested-word automata.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class NwaCegarLoop<L extends IIcfgTransition<?>> extends BasicCegarLoop<L, INestedWordAutomaton<L, IPredicate>> {

	protected static final int MINIMIZE_EVERY_KTH_ITERATION = 10;
	protected static final boolean REMOVE_DEAD_ENDS = true;
	protected static final int MINIMIZATION_TIMEOUT = 1_000;

	/**
	 * If the trace histogram max is larger than this number we try to find a danger invariant. Only used for debugging.
	 */
	private static final int DEBUG_DANGER_INVARIANTS_THRESHOLD = Integer.MAX_VALUE;

	protected final Collection<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mStoredRawInterpolantAutomata;

	private final SearchStrategy mSearchStrategy;
	private final ErrorGeneralizationEngine<L> mErrorGeneralizationEngine;

	private final boolean mUseHeuristicEmptinessCheck;
	private final ScoringMethod mScoringMethod;
	private final AStarHeuristic mAStarHeuristic;
	private final Integer mAStarRandomHeuristicSeed;

	// TODO #proofRefactor
	private final ProofUpdater<L, ?> mProofUpdater;
	protected HoareAnnotationFragments<L> mHaf;

	public <T extends IUpdateOnDifference<L> & IUpdateOnMinimization<L>> NwaCegarLoop(final DebugIdentifier name,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<? extends IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final T proofUpdater, final boolean computeHoareAnnotation, final Set<IPredicate> hoareAnnotationStates,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation,
				computeHoareAnnotation, services, transitionClazz, stateFactoryForRefinement);
		mProofUpdater = proofUpdater == null ? null : new ProofUpdater<>(proofUpdater);
		mHaf = new HoareAnnotationFragments<>(mLogger, hoareAnnotationStates);

		mErrorGeneralizationEngine = new ErrorGeneralizationEngine<>(services);

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mSearchStrategy = getSearchStrategy(prefs);
		mStoredRawInterpolantAutomata = checkStoreCounterExamples(mPref) ? new ArrayList<>() : null;

		// Heuristic Emptiness Check
		mUseHeuristicEmptinessCheck = taPrefs.useHeuristicEmptinessCheck();
		mScoringMethod = taPrefs.getHeuristicEmptinessCheckScoringMethod();
		mAStarHeuristic = taPrefs.getHeuristicEmptinessCheckAStarHeuristic();
		mAStarRandomHeuristicSeed = taPrefs.getHeuristicEmptinessCheckAStarHeuristicRandomSeed();
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction = mAbstraction;

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.EmptinessCheckTime);
		try {
			if (mUseHeuristicEmptinessCheck) {
				mCounterexample = new IsEmptyHeuristic<>(new AutomataLibraryServices(getServices()), abstraction,
						IHeuristic.getHeuristic(mAStarHeuristic, mScoringMethod, mAStarRandomHeuristicSeed))
								.getNestedRun();

				assert checkIsEmptyHeuristic(abstraction) : "IsEmptyHeuristic did not match IsEmpty";
			} else {
				mCounterexample =
						new IsEmpty<>(new AutomataLibraryServices(getServices()), abstraction, mSearchStrategy)
								.getNestedRun();
			}
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.EmptinessCheckTime);
		}

		if (mCounterexample == null) {
			return true;
		}

		if (mPref.dumpAutomata()) {
			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.DumpTime);
			mDumper.dumpNestedRun(mCounterexample);
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DumpTime);
		}
		mLogger.info("Found error trace");

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(mCounterexample.getWord());
		}
		final HistogramOfIterable<L> traceHistogram = new HistogramOfIterable<>(mCounterexample.getWord());
		mCegarLoopBenchmark.reportTraceHistogramMaximum(traceHistogram.getMax());
		if (mLogger.isInfoEnabled()) {
			mLogger.info("trace histogram " + traceHistogram.toString());
		}
		if (traceHistogram.getMax() > DEBUG_DANGER_INVARIANTS_THRESHOLD) {
			checkForDangerInvariantAndReport();
		}

		if (mPref.hasLimitTraceHistogram() && traceHistogram.getMax() > mPref.getLimitTraceHistogram()) {
			final String taskDescription =
					"bailout by trace histogram " + traceHistogram.toString() + " in iteration " + mIteration;
			throw new TaskCanceledException(UserDefinedLimit.TRACE_HISTOGRAM, getClass(), taskDescription);
		}

		return false;
	}

	private boolean checkIsEmptyHeuristic(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction)
			throws AutomataOperationCanceledException {
		final NestedRun<L, IPredicate> isEmptyHeuristicCex = (NestedRun<L, IPredicate>) mCounterexample;
		final NestedRun<L, IPredicate> isEmptyCex =
				new IsEmpty<>(new AutomataLibraryServices(getServices()), abstraction, mSearchStrategy).getNestedRun();

		final Function<NestedRun<L, IPredicate>, String> toStr =
				a -> a.getWord().asList().stream().map(b -> "T" + b.hashCode()).collect(Collectors.joining(" "));

		if (isEmptyHeuristicCex == null && isEmptyCex == null) {
			return true;
		}
		if (isEmptyHeuristicCex != null && isEmptyCex == null) {
			mLogger.fatal("IsEmptyHeuristic found a path but IsEmpty did not.");
			mLogger.fatal("IsEmptyHeuristic: " + toStr.apply(isEmptyHeuristicCex));
			return false;
		}
		if (isEmptyHeuristicCex == null && isEmptyCex != null) {
			mLogger.fatal("IsEmptyHeuristic found no path but IsEmpty did.");
			mLogger.fatal("IsEmpty         : " + toStr.apply(isEmptyCex));
			return false;
		}
		if (isEmptyHeuristicCex != null && isEmptyCex != null) {
			if (!NestedRun.isEqual(isEmptyHeuristicCex, isEmptyCex)) {
				if (isEmptyHeuristicCex.getLength() > isEmptyCex.getLength()) {
					mLogger.warn("IsEmptyHeuristic and IsEmpty found a path, but isEmptyHeuristic was longer!");
				} else {
					mLogger.info("IsEmptyHeuristic and IsEmpty found a path, but they differ");
				}
				mLogger.info("IsEmptyHeuristic: " + toStr.apply(isEmptyHeuristicCex));
				mLogger.info("IsEmpty         : " + toStr.apply(isEmptyCex));
			}
			return true;
		}
		mLogger.fatal("Should not happen");
		return false;
	}

	private boolean checkForDangerInvariantAndReport() {
		final Set<? extends IcfgEdge> allowedTransitions = PathInvariantsGenerator.extractTransitionsFromRun(
				(NestedRun<? extends IAction, IPredicate>) mCounterexample,
				mIcfg.getCfgSmtToolkit().getIcfgEdgeFactory());
		final PathProgramConstructionResult ppResult =
				PathProgram.constructPathProgram("PathInvariantsPathProgram", mIcfg, allowedTransitions);
		final IIcfg<IcfgLocation> pathProgram = ppResult.getPathProgram();
		final PredicateFactory predicateFactory = mPredicateFactory;
		final IPredicateUnifier predicateUnifier = new PredicateUnifier(mLogger, getServices(),
				mCsToolkit.getManagedScript(), predicateFactory, mCsToolkit.getSymbolTable(),
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final IPredicate precondition = predicateUnifier.getTruePredicate();
		final DangerInvariantGuesser dig = new DangerInvariantGuesser(pathProgram, getServices(), precondition,
				predicateFactory, predicateUnifier, mCsToolkit);
		final boolean hasDangerInvariant = dig.isDangerInvariant();
		if (hasDangerInvariant) {
			final Map<IcfgLocation, IPredicate> invarP = dig.getCandidateInvariant();
			final Map<IcfgLocation, Term> invarT =
					invarP.entrySet().stream().collect(Collectors.toMap(Entry::getKey, x -> x.getValue().getFormula()));
			final Set<IcfgLocation> errorLocations = IcfgUtils.getErrorLocations(pathProgram);
			final DangerInvariantResult<?, Term> res = new DangerInvariantResult<>(Activator.PLUGIN_ID, invarT,
					errorLocations, getServices().getBacktranslationService());
			getServices().getResultService().reportResult(Activator.PLUGIN_ID, res);
		}
		return hasDangerInvariant;
	}

	@Override
	protected void constructErrorAutomaton() throws AutomataOperationCanceledException {
		mErrorGeneralizationEngine.constructErrorAutomaton(mCounterexample, mPredicateFactory,
				mRefinementResult.getPredicateUnifier(), mCsToolkit, mSimplificationTechnique, mXnfConversionTechnique,
				mIcfg.getCfgSmtToolkit().getSymbolTable(), mPredicateFactoryInterpolantAutomata, mAbstraction,
				mIteration);

		mInterpolAutomaton = null;
		final NestedWordAutomaton<L, IPredicate> resultBeforeEnhancement =
				mErrorGeneralizationEngine.getResultBeforeEnhancement();
		assert isInterpolantAutomatonOfSingleStateType(resultBeforeEnhancement);
		assert accepts(getServices(), resultBeforeEnhancement, mCounterexample.getWord(),
				false) : "Error automaton broken!";
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(mIteration);
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());

		final INestedWordAutomaton<L, IPredicate> minuend = mAbstraction;

		final IPredicateUnifier predicateUnifier = mRefinementResult.getPredicateUnifier();
		final IHoareTripleChecker htc = getHoareTripleChecker();

		final AutomatonType automatonType;
		final boolean useErrorAutomaton;
		final NestedWordAutomaton<L, IPredicate> subtrahendBeforeEnhancement;
		final InterpolantAutomatonEnhancement enhanceMode;
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		final boolean exploitSigmaStarConcatOfIa;
		if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
			mErrorGeneralizationEngine.startDifference();
			automatonType = AutomatonType.ERROR;
			useErrorAutomaton = true;
			exploitSigmaStarConcatOfIa = false;
			enhanceMode = mErrorGeneralizationEngine.getEnhancementMode();
			subtrahendBeforeEnhancement = mErrorGeneralizationEngine.getResultBeforeEnhancement();
			subtrahend = mErrorGeneralizationEngine.getResultAfterEnhancement();
		} else {
			automatonType = AutomatonType.FLOYD_HOARE;
			useErrorAutomaton = false;
			// TODO #proofRefactor
			exploitSigmaStarConcatOfIa =
					!mComputeHoareAnnotation && (mProofUpdater == null || mProofUpdater.exploitSigmaStarConcatOfIa());
			subtrahendBeforeEnhancement = mInterpolAutomaton;
			enhanceMode = mPref.interpolantAutomatonEnhancement();
			subtrahend = enhanceInterpolantAutomaton(enhanceMode, predicateUnifier, htc, subtrahendBeforeEnhancement);
		}

		// TODO: HTC and predicateunifier statistics are saved in the following method, but it seems better to save them
		// at the end of the htc lifecycle instead of there
		computeAutomataDifference(minuend, subtrahend, subtrahendBeforeEnhancement, predicateUnifier,
				exploitSigmaStarConcatOfIa, htc, enhanceMode, useErrorAutomaton, automatonType);

		minimizeAbstractionIfEnabled();

		final boolean stillAccepted = new Accepts<>(new AutomataLibraryServices(getServices()),
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction,
				(NestedWord<L>) mCounterexample.getWord()).getResult();
		return !stillAccepted;
	}

	private void computeAutomataDifference(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final IPredicateUnifier predicateUnifier, final boolean explointSigmaStarConcatOfIA,
			final IHoareTripleChecker htc, final InterpolantAutomatonEnhancement enhanceMode,
			final boolean useErrorAutomaton, final AutomatonType automatonType)
			throws AutomataLibraryException, AssertionError {
		try {
			mLogger.debug("Start constructing difference");
			final PowersetDeterminizer<L, IPredicate> psd =
					new PowersetDeterminizer<>(subtrahend, true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
							minuend, subtrahend, psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
							minuend, subtrahend, psd, explointSigmaStarConcatOfIA);
				}
				mCegarLoopBenchmark.reportInterpolantAutomatonStates(subtrahend.size());
			} catch (final AutomataOperationCanceledException | ToolchainCanceledException tce) {
				final RunningTaskInfo runningTaskInfo = executeDifferenceTimeoutActions(minuend, subtrahend,
						subtrahendBeforeEnhancement, automatonType);
				tce.addRunningTaskInfo(runningTaskInfo);
				throw tce;
			} finally {
				if (enhanceMode != InterpolantAutomatonEnhancement.NONE) {
					assert subtrahend instanceof AbstractInterpolantAutomaton : "if enhancement is used, we need AbstractInterpolantAutomaton";
					((AbstractInterpolantAutomaton<L>) subtrahend).switchToReadonlyMode();
				}
			}

			if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
				mErrorGeneralizationEngine.stopDifference(minuend, mPredicateFactoryInterpolantAutomata,
						mPredicateFactoryResultChecking, mCounterexample, false);
				if (mFaultLocalizationMode != RelevanceAnalysisMode.NONE) {
					final INestedWordAutomaton<L, IPredicate> cfg = Cfg2Automaton.constructAutomatonWithSPredicates(
							getServices(), super.mIcfg, mStateFactoryForRefinement, super.mErrorLocs,
							mPref.interprocedural(), mPredicateFactory);
					mErrorGeneralizationEngine.faultLocalizationWithStorage(cfg, mCsToolkit, mPredicateFactory,
							mRefinementResult.getPredicateUnifier(), mSimplificationTechnique, mXnfConversionTechnique,
							mIcfg.getCfgSmtToolkit().getSymbolTable(), null, (NestedRun<L, IPredicate>) mCounterexample,
							(IIcfg<IcfgLocation>) mIcfg);
				}
			}

			if (mPref.dumpAutomata()) {
				final String filename =
						new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()) + "AbstractionAfterDifference";
				super.writeAutomatonToFile(subtrahend, filename);
			}
			dumpOrAppendAutomatonForReuseIfEnabled(subtrahend, predicateUnifier);

			if (!useErrorAutomaton) {
				checkEnhancement(subtrahendBeforeEnhancement, subtrahend);
			}

			if (REMOVE_DEAD_ENDS) {
				// TODO #proofRefactor
				if (mComputeHoareAnnotation) {
					final Difference<L, IPredicate> difference = (Difference<L, IPredicate>) diff;
					mHaf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
				}
				if (mProofUpdater != null) {
					final Difference<L, IPredicate> difference = (Difference<L, IPredicate>) diff;
					mProofUpdater.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
				}

				diff.removeDeadEnds();

				// TODO #proofRefactor
				if (mComputeHoareAnnotation) {
					mHaf.addDeadEndDoubleDeckers(diff);
				}
				if (mProofUpdater != null) {
					mProofUpdater.addDeadEndDoubleDeckers(diff);
				}
			}
			mAbstraction = diff.getResult();
			if (mPref.dumpAutomata()) {
				final String filename = new SubtaskIterationIdentifier(mTaskIdentifier, getIteration())
						+ "AbstractionAfterDifferenceAndDeadEndRemoval";
				super.writeAutomatonToFile(mAbstraction, filename);
			}

		} finally {
			mLogger.info(predicateUnifier.collectPredicateUnifierStatistics());
			mLogger.info(htc.getStatistics());
			mLogger.info(htc);
			mCegarLoopBenchmark.addEdgeCheckerData(htc.getStatistics());
			mCegarLoopBenchmark.addPredicateUnifierData(predicateUnifier.getPredicateUnifierBenchmark());
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		}
	}

	private RunningTaskInfo executeDifferenceTimeoutActions(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final AutomatonType automatonType) throws AutomataLibraryException {
		final RunningTaskInfo runningTaskInfo =
				getDifferenceTimeoutRunningTaskInfo(minuend, subtrahend, subtrahendBeforeEnhancement, automatonType);
		if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
			mErrorGeneralizationEngine.stopDifference(minuend, mPredicateFactoryInterpolantAutomata,
					mPredicateFactoryResultChecking, mCounterexample, true);
		}
		return runningTaskInfo;
	}

	private RunningTaskInfo getDifferenceTimeoutRunningTaskInfo(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final AutomatonType automatonType) {
		final String taskDescription = "constructing difference of abstraction (" + minuend.size() + "states) and "
				+ automatonType + " automaton (currently " + subtrahend.size() + " states, "
				+ subtrahendBeforeEnhancement.size() + " states before enhancement)";
		return new RunningTaskInfo(getClass(), taskDescription);
	}

	protected void minimizeAbstractionIfEnabled()
			throws AutomataOperationCanceledException, AutomataLibraryException, AssertionError {
		final Minimization minimization = mPref.getMinimization();
		switch (minimization) {
		case NONE:
			// do not apply minimization
			break;
		case DFA_HOPCROFT_LISTS:
		case DFA_HOPCROFT_ARRAYS:
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
		case NWA_MAX_SAT:
		case NWA_MAX_SAT2:
		case RAQ_DIRECT_SIMULATION:
		case RAQ_DIRECT_SIMULATION_B:
		case NWA_COMBINATOR_PATTERN:
		case NWA_COMBINATOR_EVERY_KTH:
		case NWA_OVERAPPROXIMATION:
		case NWA_COMBINATOR_MULTI_DEFAULT:
		case NWA_COMBINATOR_MULTI_SIMULATION:
			// apply minimization
			minimizeAbstraction(mStateFactoryForRefinement, mPredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}
	}

	/**
	 * Automata theoretic minimization of the automaton stored in mAbstraction. Expects that mAbstraction does not have
	 * dead ends.
	 *
	 * @param predicateFactoryRefinement
	 *            PredicateFactory for the construction of the new (minimized) abstraction.
	 * @param resultCheckPredFac
	 *            PredicateFactory used for auxiliary automata used for checking correctness of the result (if
	 *            assertions are enabled).
	 */
	protected void minimizeAbstraction(final PredicateFactoryRefinement predicateFactoryRefinement,
			final PredicateFactoryResultChecking resultCheckPredFac, final Minimization minimization)
			throws AutomataOperationCanceledException, AutomataLibraryException, AssertionError {

		final Function<IPredicate, Set<IcfgLocation>> lcsProvider =
				x -> (x instanceof ISLPredicate ? Collections.singleton(((ISLPredicate) x).getProgramPoint())
						: new HashSet<>(Arrays.asList(((IMLPredicate) x).getProgramPoints())));
		AutomataMinimization<Set<IcfgLocation>, IPredicate, L> am;
		try {
			// TODO #proofRefactor
			final boolean computeOld2New = mComputeHoareAnnotation || mProofUpdater != null;
			am = new AutomataMinimization<>(getServices(), mAbstraction, minimization, computeOld2New, mIteration,
					predicateFactoryRefinement, MINIMIZE_EVERY_KTH_ITERATION, mStoredRawInterpolantAutomata,
					mInterpolAutomaton, MINIMIZATION_TIMEOUT, resultCheckPredFac, lcsProvider, true);
		} catch (final AutomataMinimizationTimeout e) {
			mCegarLoopBenchmark.addAutomataMinimizationData(e.getStatistics());
			throw e.getAutomataOperationCanceledException();
		}
		mCegarLoopBenchmark.addAutomataMinimizationData(am.getStatistics());
		final boolean newAutomatonWasBuilt = am.newAutomatonWasBuilt();

		if (newAutomatonWasBuilt) {
			// postprocessing after minimization
			final IDoubleDeckerAutomaton<L, IPredicate> newAbstraction = am.getMinimizedAutomaton();

			// extract Hoare annotation
			// TODO #proofRefactor
			if (mComputeHoareAnnotation) {
				final Map<IPredicate, IPredicate> oldState2newState = am.getOldState2newStateMapping();
				if (oldState2newState == null) {
					throw new AssertionError("Hoare annotation and " + minimization + " incompatible");
				}
				mHaf.updateOnMinimization(oldState2newState, newAbstraction);
			}
			if (mProofUpdater != null) {
				final Map<IPredicate, IPredicate> oldState2newState = am.getOldState2newStateMapping();
				if (oldState2newState == null) {
					throw new AssertionError("Proof production and " + minimization + " incompatible");
				}
				mProofUpdater.updateOnMinimization(oldState2newState, newAbstraction);
			}

			// statistics
			final int oldSize = mAbstraction.size();
			final int newSize = newAbstraction.size();
			assert oldSize == 0 || oldSize >= newSize : "Minimization increased state space";

			// use result
			mAbstraction = newAbstraction;
		}
	}

	@Override
	protected void finish() {
		mErrorGeneralizationEngine.reportErrorGeneralizationBenchmarks();
		super.finish();
	}

	@Override
	protected void computeIcfgHoareAnnotation() {
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.HoareAnnotationTime.toString());
		try {
			final HoareAnnotationComposer clha = computeHoareAnnotationComposer();
			final HoareAnnotationWriter writer = new HoareAnnotationWriter(mIcfg, mCsToolkit, mPredicateFactory, clha,
					mServices, mSimplificationTechnique, mXnfConversionTechnique);
			// writer.addHoareAnnotationToCFG();
			mCegarLoopBenchmark.addHoareAnnotationData(clha.getHoareAnnotationStatisticsGenerator());
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.HoareAnnotationTime.toString());
		}
	}

	protected HoareAnnotationComposer computeHoareAnnotationComposer() {
		if (mCsToolkit.getManagedScript().isLocked()) {
			throw new AssertionError("SMTManager must not be locked at the beginning of Hoare annotation computation");
		}
		final INestedWordAutomaton<L, IPredicate> abstraction = mAbstraction;
		new HoareAnnotationExtractor<>(mServices, abstraction, mHaf);
		final HoareAnnotationComposer clha = new HoareAnnotationComposer(mCsToolkit, mPredicateFactory, mHaf, mServices,
				mSimplificationTechnique, mXnfConversionTechnique);
		return clha;
	}

	private static final boolean checkStoreCounterExamples(final TAPreferences pref) {
		return pref.getMinimization() == Minimization.NWA_OVERAPPROXIMATION;
	}

	private static SearchStrategy getSearchStrategy(final IPreferenceProvider mPrefs) {
		switch (mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_COUNTEREXAMPLE_SEARCH_STRATEGY,
				CounterexampleSearchStrategy.class)) {
		case BFS:
			return SearchStrategy.BFS;
		case DFS:
			return SearchStrategy.DFS;
		default:
			throw new IllegalArgumentException();
		}
	}

	// Annoyingly, this wrapper seems currently necessary due to Java's limited support for intersection types.
	// The alternative is including a type parameter as below in the NwaCegarLoop itself.
	private static final class ProofUpdater<L, T extends IUpdateOnMinimization<L> & IUpdateOnDifference<L>>
			implements IUpdateOnMinimization<L>, IUpdateOnDifference<L> {
		private final T mUpdater;

		public ProofUpdater(final T updater) {
			mUpdater = updater;
		}

		@Override
		public boolean exploitSigmaStarConcatOfIa() {
			return mUpdater.exploitSigmaStarConcatOfIa();
		}

		@Override
		public void updateOnIntersection(
				final Map<IPredicate, Map<IPredicate, ProductNwa<L, IPredicate>.ProductState>> fst2snd2res,
				final IDoubleDeckerAutomaton<L, IPredicate> result) {
			mUpdater.updateOnIntersection(fst2snd2res, result);
		}

		@Override
		public void addDeadEndDoubleDeckers(final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff) {
			mUpdater.addDeadEndDoubleDeckers(diff);
		}

		@Override
		public void updateOnMinimization(final Map<IPredicate, IPredicate> old2New,
				final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction) {
			mUpdater.updateOnMinimization(old2New, abstraction);
		}
	}
}
