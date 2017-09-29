/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.SubtaskFileIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.LineCoverageCalculator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization.FlowSensitiveFaultLocalizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.InterpolantAutomatonBuilderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.CounterexampleSearchStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.RefinementStrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.interactive.InteractiveRefinementStrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessProductAutomaton;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * Subclass of AbstractCegarLoop which provides all algorithms for checking safety (not termination).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class BasicCegarLoop<LETTER extends IIcfgTransition<?>> extends AbstractCegarLoop<LETTER> {

	protected static final int MINIMIZE_EVERY_KTH_ITERATION = 10;
	protected static final boolean REMOVE_DEAD_ENDS = true;
	protected static final boolean TRACE_HISTOGRAMM_BAILOUT = false;
	protected static final int MINIMIZATION_TIMEOUT = 1_000;
	private static final boolean NON_EA_INDUCTIVITY_CHECK = false;

	protected final PredicateFactoryRefinement mStateFactoryForRefinement;
	protected final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	protected final PredicateFactoryResultChecking mPredicateFactoryResultChecking;

	private final CegarAbsIntRunner<LETTER> mAbsIntRunner;
	private final InterpolantAutomatonBuilderFactory<LETTER> mInterpolantAutomatonBuilderFactory;
	protected final InterpolationTechnique mInterpolation;
	protected final InterpolantAutomaton mInterpolantAutomatonConstructionProcedure;
	protected final UnsatCores mUnsatCores;
	protected final boolean mUseLiveVariables;

	protected final boolean mComputeHoareAnnotation;
	protected final AssertCodeBlockOrder mAssertCodeBlocksIncrementally;

	private final boolean mDoFaultLocalizationNonFlowSensitive;
	private final boolean mDoFaultLocalizationFlowSensitive;
	private final Set<IcfgLocation> mHoareAnnotationLocations;

	protected final Collection<INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>> mStoredRawInterpolantAutomata;

	private final SearchStrategy mSearchStrategy;

	private final RefinementStrategyFactory<LETTER> mRefinementStrategyFactory;
	private final PathProgramDumpController<LETTER> mPathProgramDumpController;

	protected boolean mFallbackToFpIfInterprocedural = false;
	protected HoareAnnotationFragments<LETTER> mHaf;
	private INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> mWitnessAutomaton;
	protected IRefinementEngine<NestedWordAutomaton<LETTER, IPredicate>> mTraceCheckAndRefinementEngine;

	private final ErrorGeneralizationEngine<LETTER> mErrorGeneralizationEngine;
	private final PathProgramCache<LETTER> mPathProgramCache;
	private final boolean mStoreFloydHoareAutomata;
	private final LinkedHashSet<AbstractInterpolantAutomaton<LETTER>> mFloydHoareAutomata = new LinkedHashSet<>();
	protected final TaskIdentifier mTaskIdentifier;

	public BasicCegarLoop(final String name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		super(services, storage, name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs,
				services.getLoggingService().getLogger(Activator.PLUGIN_ID));
		// TODO: TaskIdentifier should probably be provided by caller
		mTaskIdentifier = new SubtaskFileIdentifier(null, mIcfg.getIdentifier());
		mPathProgramDumpController = new PathProgramDumpController<>(mServices, mPref, mIcfg);
		if (mFallbackToFpIfInterprocedural && rootNode.getProcedureEntryNodes().size() > 1) {
			if (interpolation == InterpolationTechnique.FPandBP) {
				mLogger.info("fallback from FPandBP to FP because CFG is interprocedural");
				mInterpolation = InterpolationTechnique.ForwardPredicates;
			} else {
				mInterpolation = interpolation;
			}
			if (mPref.interpolantAutomaton() == InterpolantAutomaton.TWOTRACK) {
				mInterpolantAutomatonConstructionProcedure = InterpolantAutomaton.CANONICAL;
			} else {
				mInterpolantAutomatonConstructionProcedure = mPref.interpolantAutomaton();
			}
		} else {
			mInterpolation = interpolation;
			mInterpolantAutomatonConstructionProcedure = mPref.interpolantAutomaton();
		}
		mComputeHoareAnnotation = computeHoareAnnotation;
		if (mComputeHoareAnnotation) {
			mHoareAnnotationLocations = (Set<IcfgLocation>) TraceAbstractionUtils
					.getLocationsForWhichHoareAnnotationIsComputed(rootNode, mPref.getHoareAnnotationPositions());
		} else {
			mHoareAnnotationLocations = Collections.emptySet();
		}
		mStoreFloydHoareAutomata = (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE);
		mErrorGeneralizationEngine = new ErrorGeneralizationEngine<>(services);
		mHaf = new HoareAnnotationFragments<>(mLogger, mHoareAnnotationLocations, mPref.getHoareAnnotationPositions());
		mStateFactoryForRefinement = new PredicateFactoryRefinement(mServices, super.mCsToolkit.getManagedScript(),
				predicateFactory, mPref.computeHoareAnnotation(), mHoareAnnotationLocations);
		mPredicateFactoryInterpolantAutomata = new PredicateFactoryForInterpolantAutomata(
				super.mCsToolkit.getManagedScript(), mPredicateFactory, mPref.computeHoareAnnotation());

		mAssertCodeBlocksIncrementally = mServices.getPreferenceProvider(Activator.PLUGIN_ID).getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY,
				AssertCodeBlockOrder.class);

		mPredicateFactoryResultChecking = new PredicateFactoryResultChecking(mPredicateFactory);

		mCegarLoopBenchmark = new CegarLoopStatisticsGenerator();
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.OverallTime.toString());

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mUnsatCores = prefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES, UnsatCores.class);
		mUseLiveVariables = prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_LIVE_VARIABLES);
		mDoFaultLocalizationNonFlowSensitive = prefs.getBoolean(
				TraceAbstractionPreferenceInitializer.LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS_NON_FLOW_SENSITIVE);
		mDoFaultLocalizationFlowSensitive = prefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS_FLOW_SENSITIVE);

		mPathProgramCache = new PathProgramCache<>(mLogger);
		mAbsIntRunner = new CegarAbsIntRunner<>(services, mCegarLoopBenchmark, rootNode, mSimplificationTechnique,
				mXnfConversionTechnique, mCsToolkit, mPathProgramCache);
		mInterpolantAutomatonBuilderFactory = new InterpolantAutomatonBuilderFactory<>(mServices, mCsToolkit,
				mPredicateFactoryInterpolantAutomata, mIcfg, mAbsIntRunner, taPrefs, mInterpolation,
				mInterpolantAutomatonConstructionProcedure, mCegarLoopBenchmark);

		mSearchStrategy = getSearchStrategy(prefs);
		mStoredRawInterpolantAutomata = checkStoreCounterExamples(mPref) ? new ArrayList<>() : null;

		final TaCheckAndRefinementPreferences<LETTER> taCheckAndRefinementPrefs = new TaCheckAndRefinementPreferences<>(
				mServices, mPref, mInterpolation, mSimplificationTechnique, mXnfConversionTechnique, mCsToolkit,
				mPredicateFactory, mIcfg, mToolchainStorage, mInterpolantAutomatonBuilderFactory);

		if (mInteractive.isInteractiveMode()) {
			mRefinementStrategyFactory = new InteractiveRefinementStrategyFactory<>(mLogger, mServices,
					mToolchainStorage, mInteractive, mPref, taCheckAndRefinementPrefs, mAbsIntRunner, mIcfg,
					mPredicateFactory, mPathProgramCache);
		} else {
			mRefinementStrategyFactory = new RefinementStrategyFactory<>(mLogger, mServices, mToolchainStorage, mPref,
					taCheckAndRefinementPrefs, mAbsIntRunner, mIcfg, mPredicateFactory, mPathProgramCache);
		}
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		final CFG2NestedWordAutomaton<LETTER> cFG2NestedWordAutomaton = new CFG2NestedWordAutomaton<>(mServices,
				mPref.interprocedural(), super.mCsToolkit, super.mPredicateFactory, mLogger);

		mAbstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(super.mIcfg, mStateFactoryForRefinement,
				super.mErrorLocs);
		if (mComputeHoareAnnotation
				&& mPref.getHoareAnnotationPositions() == HoareAnnotationPositions.LoopsAndPotentialCycles) {
			final INestedWordAutomaton<LETTER, IPredicate> nwa =
					(INestedWordAutomaton<LETTER, IPredicate>) mAbstraction;
			for (final IPredicate pred : nwa.getStates()) {
				for (final OutgoingCallTransition<LETTER, IPredicate> trans : nwa.callSuccessors(pred)) {
					mHoareAnnotationLocations.add(((ISLPredicate) pred).getProgramPoint());
					mHoareAnnotationLocations.add(((ISLPredicate) trans.getSucc()).getProgramPoint());
				}
			}
		}
		if (mWitnessAutomaton != null) {
			final WitnessProductAutomaton<LETTER> wpa = new WitnessProductAutomaton<>(mServices,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, mWitnessAutomaton,
					mCsToolkit, mPredicateFactory, mStateFactoryForRefinement);
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> test =
					new RemoveUnreachable<>(new AutomataLibraryServices(mServices), wpa).getResult();
			mLogger.info("Full witness product has " + test.sizeInformation());
			mLogger.info(wpa.generateBadWitnessInformation());
			final LineCoverageCalculator<LETTER> origCoverage = new LineCoverageCalculator<>(mServices, mAbstraction);
			mAbstraction = new RemoveDeadEnds<>(new AutomataLibraryServices(mServices), wpa).getResult();
			new LineCoverageCalculator<>(mServices, mAbstraction, origCoverage).reportCoverage("Witness product");
		}
		mInteractive.send(mAbstraction);
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction =
				(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction;
		// TODO: Make an option out of this
		mCounterexample =
				new IsEmpty<>(new AutomataLibraryServices(mServices), abstraction, mSearchStrategy).getNestedRun();

		// mCounterexample = new IsEmptyHeuristic<>(new AutomataLibraryServices(mServices), abstraction).getNestedRun();

		if (mCounterexample == null) {
			return true;
		}

		if (mInteractive.isInteractiveMode()) {
			if (mInteractive.getPreferences().ismCEXS()) {
				// TODO: send mCounterexample as "preview"
				mInteractive.getInterface().common()
						.send("Select a Trace: Please select the trace you want Ultimate to analyze next.");
				mCounterexample = mInteractive.getUserRun(abstraction, mIteration, mServices, mSearchStrategy,
						mStateFactoryForRefinement, mPredicateFactory, mCsToolkit.getManagedScript());
			}
			mInteractive.send(mCounterexample);
		}

		if (mPref.dumpAutomata()) {
			mDumper.dumpNestedRun(mCounterexample);
		}
		mLogger.info("Found error trace");
		mPathProgramCache.addRun(mCounterexample);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(mCounterexample.getWord());
		}
		final HistogramOfIterable<LETTER> traceHistogram = new HistogramOfIterable<>(mCounterexample.getWord());
		mCegarLoopBenchmark.reportTraceHistogramMaximum(traceHistogram.getMax());
		if (mLogger.isInfoEnabled()) {
			mLogger.info("trace histogram " + traceHistogram.toString());
		}
		if (TRACE_HISTOGRAMM_BAILOUT && traceHistogram.getMax() > traceHistogram.getVisualizationArray().length) {
			final String message = "bailout by trace histogram " + traceHistogram.toString();
			final String taskDescription = "trying to verify (iteration " + mIteration + ")";
			throw new ToolchainCanceledException(message, getClass(), taskDescription);
		}
		// Don't send the histogram: the complete run is sent already.
		// mInteractive.send(traceHistogram);
		return false;
	}

	@Override
	protected LBool isCounterexampleFeasible() throws AutomataOperationCanceledException {

		final IRefinementStrategy<LETTER> strategy = mRefinementStrategyFactory.createStrategy(
				mPref.getRefinementStrategy(), mCounterexample, mAbstraction, 
				new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()));
		try {
			mTraceCheckAndRefinementEngine = new TraceAbstractionRefinementEngine<>(mLogger, strategy, mInteractive);
		} catch (final ToolchainCanceledException tce) {
			final int traceHistogramMax = new HistogramOfIterable<>(mCounterexample.getWord()).getMax();
			final String taskDescription = "analyzing trace of length " + mCounterexample.getLength()
					+ " with TraceHistMax " + traceHistogramMax;
			tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
			throw tce;
		}

		final IPredicateUnifier predicateUnifier = mTraceCheckAndRefinementEngine.getPredicateUnifier();
		final LBool feasibility = mTraceCheckAndRefinementEngine.getCounterexampleFeasibility();

		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample might be feasible");
			if (mTraceCheckAndRefinementEngine.providesICfgProgramExecution()) {
				mRcfgProgramExecution = mTraceCheckAndRefinementEngine.getIcfgProgramExecution();
			} else {
				mRcfgProgramExecution =
						TraceCheckerUtils.computeSomeIcfgProgramExecutionWithoutValues(mCounterexample.getWord());
			}

			if ((mDoFaultLocalizationNonFlowSensitive || mDoFaultLocalizationFlowSensitive)
					&& feasibility == LBool.SAT) {
				final CFG2NestedWordAutomaton<LETTER> cFG2NestedWordAutomaton = new CFG2NestedWordAutomaton<>(mServices,
						mPref.interprocedural(), super.mCsToolkit, mPredicateFactory, mLogger);
				final INestedWordAutomaton<LETTER, IPredicate> cfg = cFG2NestedWordAutomaton
						.getNestedWordAutomaton(super.mIcfg, mStateFactoryForRefinement, super.mErrorLocs);
				final FlowSensitiveFaultLocalizer<LETTER> a = new FlowSensitiveFaultLocalizer<>(
						(NestedRun<LETTER, IPredicate>) mCounterexample, cfg, mServices, mCsToolkit, mPredicateFactory,
						mCsToolkit.getModifiableGlobalsTable(), predicateUnifier, mDoFaultLocalizationNonFlowSensitive,
						mDoFaultLocalizationFlowSensitive, mSimplificationTechnique, mXnfConversionTechnique,
						mIcfg.getCfgSmtToolkit().getSymbolTable());
				mRcfgProgramExecution = mRcfgProgramExecution.addRelevanceInformation(a.getRelevanceInformation());
			}
		} else {
			mPathProgramDumpController.reportPathProgram((NestedRun<LETTER, IPredicate>) mCounterexample,
					((TraceAbstractionRefinementEngine<LETTER>) mTraceCheckAndRefinementEngine)
							.somePerfectSequenceFound(),
					mIteration);
		}

		if (mInteractive.isInteractiveMode() && feasibility == LBool.SAT) {
			mInteractive.getInterface().common()
					.send("Feasible Counterexample:The Counterexample trace analyzed in iteration " + mIteration
							+ " was feasible.");
		}

		mCegarLoopBenchmark.addRefinementEngineStatistics(strategy.getRefinementEngineStatistics());
		return feasibility;
	}

	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		mInterpolAutomaton = mTraceCheckAndRefinementEngine.getInfeasibilityProof();
		assert isInterpolantAutomatonOfSingleStateType(mInterpolAutomaton);
		if (NON_EA_INDUCTIVITY_CHECK) {
			final boolean inductive = new InductivityCheck<>(mServices, mInterpolAutomaton, false, true,
					new IncrementalHoareTripleChecker(super.mCsToolkit)).getResult();

			if (!inductive) {
				throw new AssertionError("not inductive");
			}
		}

		assert accepts(mServices, mInterpolAutomaton, mCounterexample.getWord()) : "Interpolant automaton broken!";
		assert new InductivityCheck<>(mServices, mInterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(super.mCsToolkit)).getResult();
	}

	private static boolean
			isInterpolantAutomatonOfSingleStateType(final INestedWordAutomaton<?, IPredicate> automaton) {
		Class<? extends IPredicate> typeofState = null;
		for (final IPredicate state : automaton.getStates()) {
			if (typeofState == null) {
				typeofState = state.getClass();
			}
			if (state.getClass() != typeofState) {
				return false;
			}
		}
		return true;
	}

	@Override
	protected void constructErrorAutomaton() throws AutomataOperationCanceledException {
		mErrorGeneralizationEngine.constructErrorAutomaton(mCounterexample, mPredicateFactory,
				mTraceCheckAndRefinementEngine.getPredicateUnifier(), mCsToolkit, mSimplificationTechnique,
				mXnfConversionTechnique, mIcfg.getCfgSmtToolkit().getSymbolTable(),
				mPredicateFactoryInterpolantAutomata, (INestedWordAutomaton<LETTER, IPredicate>) mAbstraction,
				mIteration);

		mInterpolAutomaton = null;
		final NestedWordAutomaton<LETTER, IPredicate> resultBeforeEnhancement =
				mErrorGeneralizationEngine.getResultBeforeEnhancement();
		assert isInterpolantAutomatonOfSingleStateType(resultBeforeEnhancement);
		assert accepts(mServices, resultBeforeEnhancement, mCounterexample.getWord()) : "Error automaton broken!";
	}

	@Override
	protected void reportErrorAutomatonBenchmarks() {
		mErrorGeneralizationEngine.reportErrorGeneralizationBenchmarks();
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		final IPredicateUnifier predicateUnifier = mTraceCheckAndRefinementEngine.getPredicateUnifier();
		mStateFactoryForRefinement.setIteration(mIteration);
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());

		final INestedWordAutomaton<LETTER, IPredicate> minuend =
				(INestedWordAutomaton<LETTER, IPredicate>) mAbstraction;

		final IHoareTripleChecker htc;
		if (mTraceCheckAndRefinementEngine.getHoareTripleChecker() != null) {
			htc = mTraceCheckAndRefinementEngine.getHoareTripleChecker();
		} else {
			htc = TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
					mPref.getHoareTripleChecks(), mCsToolkit, mTraceCheckAndRefinementEngine.getPredicateUnifier());
		}

		final String automatonType;
		final boolean useErrorAutomaton;
		final NestedWordAutomaton<LETTER, IPredicate> subtrahendBeforeEnhancement;
		final InterpolantAutomatonEnhancement enhanceMode;
		final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> subtrahend;
		final boolean exploitSigmaStarConcatOfIa;
		if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
			mErrorGeneralizationEngine.startDifference();
			automatonType = "error";
			useErrorAutomaton = true;
			exploitSigmaStarConcatOfIa = false;
			enhanceMode = mErrorGeneralizationEngine.getEnhancementMode();
			subtrahendBeforeEnhancement = mErrorGeneralizationEngine.getResultBeforeEnhancement();
			subtrahend = mErrorGeneralizationEngine.getResultAfterEnhancement();
		} else {
			automatonType = "interpolant";
			useErrorAutomaton = false;
			exploitSigmaStarConcatOfIa = !mComputeHoareAnnotation;
			subtrahendBeforeEnhancement = mInterpolAutomaton;
			enhanceMode = mPref.interpolantAutomatonEnhancement();
			if (enhanceMode == InterpolantAutomatonEnhancement.NONE) {
				subtrahend = subtrahendBeforeEnhancement;
			} else {
				final AbstractInterpolantAutomaton<LETTER> ia = constructInterpolantAutomatonForOnDemandEnhancement(
						subtrahendBeforeEnhancement, predicateUnifier, htc, enhanceMode);
				subtrahend = ia;
				if (mStoreFloydHoareAutomata) {
					mFloydHoareAutomata.add(ia);
				}
			}
		}

		computeAutomataDifference(minuend, subtrahend, subtrahendBeforeEnhancement, predicateUnifier,
				exploitSigmaStarConcatOfIa, htc, enhanceMode, useErrorAutomaton, automatonType);

		mLogger.info(predicateUnifier.collectPredicateUnifierStatistics());

		minimizeAbstractionIfEnabled();

		final boolean stillAccepted = new Accepts<>(new AutomataLibraryServices(mServices),
				(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction,
				(NestedWord<LETTER>) mCounterexample.getWord()).getResult();
		return !stillAccepted;
	}

	private void computeAutomataDifference(final INestedWordAutomaton<LETTER, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> subtrahendBeforeEnhancement,
			final IPredicateUnifier predicateUnifier, final boolean explointSigmaStarConcatOfIA,
			final IHoareTripleChecker htc, final InterpolantAutomatonEnhancement enhanceMode,
			final boolean useErrorAutomaton, final String automatonType)
			throws AutomataLibraryException, AutomataOperationCanceledException, AssertionError {
		try {
			mLogger.debug("Start constructing difference");
			final PowersetDeterminizer<LETTER, IPredicate> psd =
					new PowersetDeterminizer<>(subtrahend, true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<LETTER, IPredicate> diff;
			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
							minuend, subtrahend, psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement, minuend,
							subtrahend, psd, explointSigmaStarConcatOfIA);
				}
			} catch (final AutomataOperationCanceledException aoce) {
				final RunningTaskInfo runningTaskInfo = executeDifferenceTimeoutActions(minuend, subtrahend,
						subtrahendBeforeEnhancement, automatonType);
				aoce.addRunningTaskInfo(runningTaskInfo);
				throw aoce;
			} catch (final ToolchainCanceledException tce) {
				final RunningTaskInfo runningTaskInfo = executeDifferenceTimeoutActions(minuend, subtrahend,
						subtrahendBeforeEnhancement, automatonType);
				tce.addRunningTaskInfo(runningTaskInfo);
				throw tce;
			} finally {
				if (enhanceMode != InterpolantAutomatonEnhancement.NONE) {
					assert subtrahend instanceof AbstractInterpolantAutomaton : "if enhancement is used, we need AbstractInterpolantAutomaton";
					((AbstractInterpolantAutomaton<LETTER>) subtrahend).switchToReadonlyMode();
				}
			}

			if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
				mErrorGeneralizationEngine.stopDifference(minuend, mPredicateFactoryInterpolantAutomata,
						mPredicateFactoryResultChecking, mCounterexample, false);
				final CFG2NestedWordAutomaton<LETTER> cFG2NestedWordAutomaton = new CFG2NestedWordAutomaton<>(mServices,
						mPref.interprocedural(), super.mCsToolkit, mPredicateFactory, mLogger);
				final INestedWordAutomaton<LETTER, IPredicate> cfg = cFG2NestedWordAutomaton
						.getNestedWordAutomaton(super.mIcfg, mStateFactoryForRefinement, super.mErrorLocs);
				mErrorGeneralizationEngine.faultLocalizationWithStorage(cfg, mCsToolkit, mPredicateFactory,
						mTraceCheckAndRefinementEngine.getPredicateUnifier(), mSimplificationTechnique,
						mXnfConversionTechnique, mIcfg.getCfgSmtToolkit().getSymbolTable(), null,
						(NestedRun<LETTER, IPredicate>) mCounterexample);
			}

			dumpAutomatonIfEnabled(subtrahend, "", automatonType);

			if (!useErrorAutomaton) {
				checkEnhancement(subtrahendBeforeEnhancement, subtrahend);
			}

			if (REMOVE_DEAD_ENDS) {
				if (mComputeHoareAnnotation) {
					final Difference<LETTER, IPredicate> difference = (Difference<LETTER, IPredicate>) diff;
					mHaf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
				}
				diff.removeDeadEnds();
				if (mComputeHoareAnnotation) {
					mHaf.addDeadEndDoubleDeckers(diff);
				}
			}
			mAbstraction = diff.getResult();

			dumpAutomatonIfEnabled(subtrahendBeforeEnhancement, "Enhanced", automatonType);
		} finally {
			mCegarLoopBenchmark.addEdgeCheckerData(htc.getEdgeCheckerBenchmark());
			mCegarLoopBenchmark.addPredicateUnifierData(predicateUnifier.getPredicateUnifierBenchmark());
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		}
	}

	private RunningTaskInfo executeDifferenceTimeoutActions(final INestedWordAutomaton<LETTER, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> subtrahendBeforeEnhancement,
			final String automatonType) throws AutomataLibraryException {
		final RunningTaskInfo runningTaskInfo =
				getDifferenceTimeoutRunningTaskInfo(minuend, subtrahend, subtrahendBeforeEnhancement, automatonType);
		if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
			mErrorGeneralizationEngine.stopDifference(minuend, mPredicateFactoryInterpolantAutomata,
					mPredicateFactoryResultChecking, mCounterexample, true);
		}
		return runningTaskInfo;
	}

	private RunningTaskInfo getDifferenceTimeoutRunningTaskInfo(final INestedWordAutomaton<LETTER, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> subtrahendBeforeEnhancement,
			final String automatonType) {
		final String taskDescription = "constructing difference of abstraction (" + minuend.size() + "states) and "
				+ automatonType + " automaton (currently " + subtrahend.size() + " states, "
				+ subtrahendBeforeEnhancement.size() + " states before enhancement)";
		return new RunningTaskInfo(getClass(), taskDescription);
	}

	private void dumpAutomatonIfEnabled(final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> subtrahend,
			final String prefix, final String automatonType) {
		if (mPref.dumpAutomata()) {
			final String type = Character.toUpperCase(automatonType.charAt(0)) + automatonType.substring(1);
			final String filename = prefix + type + "Automaton_Iteration" + mIteration;
			super.writeAutomatonToFile(subtrahend, filename);
		}
	}

	private void checkEnhancement(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> inputInterpolantAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException, AssertionError, AutomataOperationCanceledException {
		if (!new Accepts<>(new AutomataLibraryServices(mServices), interpolantAutomaton,
				(NestedWord<LETTER>) mCounterexample.getWord(), true, false).getResult()) {

			final boolean isOriginalBroken = !new Accepts<>(new AutomataLibraryServices(mServices),
					inputInterpolantAutomaton, (NestedWord<LETTER>) mCounterexample.getWord(), true, false).getResult();
			try {
				debugLogBrokenInterpolantAutomaton(inputInterpolantAutomaton, interpolantAutomaton, mCounterexample);
			} catch (final Error e) {
				// suppress any exception, throw assertion error instead
			}
			throw new AssertionError("enhanced interpolant automaton in iteration " + mIteration
					+ " broken: counterexample of length " + mCounterexample.getLength() + " not accepted"
					+ (isOriginalBroken ? " (original was already broken)" : " (original is ok)"));
		}
		assert isInterpolantAutomatonOfSingleStateType(
				new RemoveUnreachable<>(new AutomataLibraryServices(mServices), interpolantAutomaton).getResult());
		assert new InductivityCheck<>(mServices,
				new RemoveUnreachable<>(new AutomataLibraryServices(mServices), interpolantAutomaton).getResult(),
				false, true, new IncrementalHoareTripleChecker(super.mCsToolkit)).getResult();
	}

	private void debugLogBrokenInterpolantAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolantAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> enhancedInterpolantAutomaton,
			final IRun<LETTER, IPredicate, ?> counterexample) {
		mLogger.fatal("--");
		mLogger.fatal("enhanced interpolant automaton broken: counterexample not accepted");
		mLogger.fatal("word:");
		for (final LETTER letter : counterexample.getWord()) {
			mLogger.fatal(letter);
		}
		mLogger.fatal("original automaton:");
		mLogger.fatal(interpolantAutomaton);
		mLogger.fatal("enhanced automaton:");
		mLogger.fatal(enhancedInterpolantAutomaton);
		mLogger.fatal("--");
	}

	private AbstractInterpolantAutomaton<LETTER>
			constructInterpolantAutomatonForOnDemandEnhancement(
					final NestedWordAutomaton<LETTER, IPredicate> inputInterpolantAutomaton,
					final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
					final InterpolantAutomatonEnhancement enhanceMode) {
		final AbstractInterpolantAutomaton<LETTER> result;
		switch (enhanceMode) {
		case NONE:
			throw new IllegalArgumentException("In setting NONE we will not do any enhancement");
		case PREDICATE_ABSTRACTION:
		case PREDICATE_ABSTRACTION_CONSERVATIVE:
		case PREDICATE_ABSTRACTION_CANNIBALIZE:
			result = constructInterpolantAutomatonForOnDemandEnhancementPredicateAbstraction(inputInterpolantAutomaton,
					htc, enhanceMode);
			break;
		case EAGER:
		case NO_SECOND_CHANCE:
		case EAGER_CONSERVATIVE:
			result = constructInterpolantAutomatonForOnDemandEnhancementEager(inputInterpolantAutomaton,
					predicateUnifier, htc, enhanceMode);
			break;
		default:
			throw new UnsupportedOperationException("unknown " + enhanceMode);
		}
		return result;
	}

	private NondeterministicInterpolantAutomaton<LETTER> constructInterpolantAutomatonForOnDemandEnhancementEager(
			final NestedWordAutomaton<LETTER, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		final boolean conservativeSuccessorCandidateSelection =
				enhanceMode == InterpolantAutomatonEnhancement.EAGER_CONSERVATIVE;
		final boolean secondChance = enhanceMode != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE;
		return new NondeterministicInterpolantAutomaton<>(mServices, mCsToolkit, htc, inputInterpolantAutomaton,
				predicateUnifier, conservativeSuccessorCandidateSelection, secondChance);
	}

	private DeterministicInterpolantAutomaton<LETTER>
			constructInterpolantAutomatonForOnDemandEnhancementPredicateAbstraction(
					final NestedWordAutomaton<LETTER, IPredicate> inputInterpolantAutomaton,
					final IHoareTripleChecker htc, final InterpolantAutomatonEnhancement enhanceMode) {
		final boolean conservativeSuccessorCandidateSelection =
				enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE;
		final boolean cannibalize = enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE;
		return new DeterministicInterpolantAutomaton<>(mServices, mCsToolkit, htc, inputInterpolantAutomaton,
				mTraceCheckAndRefinementEngine.getPredicateUnifier(), conservativeSuccessorCandidateSelection,
				cannibalize);
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
	protected void minimizeAbstraction(final PredicateFactoryForInterpolantAutomata predicateFactoryRefinement,
			final PredicateFactoryResultChecking resultCheckPredFac, final Minimization minimization)
			throws AutomataOperationCanceledException, AutomataLibraryException, AssertionError {

		if (mPref.dumpAutomata()) {
			final String filename =
					mIcfg.getIdentifier() + "_DiffAutomatonBeforeMinimization_Iteration" + mIteration;
			super.writeAutomatonToFile(mAbstraction, filename);
		}
		final Function<ISLPredicate, IcfgLocation> lcsProvider = x -> x.getProgramPoint();
		AutomataMinimization<IcfgLocation, ISLPredicate, LETTER> am;
		try {
			am = new AutomataMinimization<>(mServices, (INestedWordAutomaton<LETTER, IPredicate>) mAbstraction,
					minimization, mComputeHoareAnnotation, mIteration, predicateFactoryRefinement,
					MINIMIZE_EVERY_KTH_ITERATION, mStoredRawInterpolantAutomata, mInterpolAutomaton,
					MINIMIZATION_TIMEOUT, resultCheckPredFac, lcsProvider, true);
		} catch (final AutomataMinimizationTimeout e) {
			mCegarLoopBenchmark.addAutomataMinimizationData(e.getStatistics());
			throw e.getAutomataOperationCanceledException();
		}
		mCegarLoopBenchmark.addAutomataMinimizationData(am.getStatistics());
		final boolean newAutomatonWasBuilt = am.newAutomatonWasBuilt();

		if (newAutomatonWasBuilt) {
			// postprocessing after minimization
			final IDoubleDeckerAutomaton<LETTER, IPredicate> newAbstraction = am.getMinimizedAutomaton();

			// extract Hoare annotation
			if (mComputeHoareAnnotation) {
				final Map<IPredicate, IPredicate> oldState2newState = am.getOldState2newStateMapping();
				if (oldState2newState == null) {
					throw new AssertionError("Hoare annotation and " + minimization + " incompatible");
				}
				mHaf.updateOnMinimization(oldState2newState, newAbstraction);
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
	protected void computeCFGHoareAnnotation() {
		if (mCsToolkit.getManagedScript().isLocked()) {
			throw new AssertionError("SMTManager must not be locked at the beginning of Hoare annotation computation");
		}
		final INestedWordAutomaton<LETTER, IPredicate> abstraction =
				(INestedWordAutomaton<LETTER, IPredicate>) mAbstraction;
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.HoareAnnotationTime.toString());
		new HoareAnnotationExtractor<>(mServices, abstraction, mHaf);
		final HoareAnnotationComposer clha = new HoareAnnotationComposer(mCsToolkit, mPredicateFactory, mHaf, mServices,
				mSimplificationTechnique, mXnfConversionTechnique);
		final HoareAnnotationWriter writer = new HoareAnnotationWriter(mIcfg, mCsToolkit, mPredicateFactory,
				clha, mServices, mSimplificationTechnique, mXnfConversionTechnique);
		writer.addHoareAnnotationToCFG();
		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.HoareAnnotationTime.toString());
		mCegarLoopBenchmark.addHoareAnnotationData(clha.getHoareAnnotationStatisticsGenerator());
	}

	@Override
	public IElement getArtifact() {
		if (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.INTERPOLANT_AUTOMATON
				|| mPref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {

			if (mArtifactAutomaton == null) {
				mLogger.warn("Preferred Artifact not available," + " visualizing the RCFG instead");
				return mIcfg;
			}
			try {
				return mArtifactAutomaton.transformToUltimateModel(new AutomataLibraryServices(mServices));
			} catch (final AutomataOperationCanceledException e) {
				return null;
			}
		} else if (mPref.artifact() == Artifact.RCFG) {
			return mIcfg;
		} else {
			throw new IllegalArgumentException();
		}
	}

	protected boolean accepts(final IUltimateServiceProvider services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> nia, final Word<LETTER> word)
			throws AutomataOperationCanceledException {
		try {
			return new Accepts<>(new AutomataLibraryServices(services), nia, NestedWord.nestedWord(word), false, false)
					.getResult();
		} catch (final AutomataOperationCanceledException e) {
			throw e;
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}

	public CegarLoopStatisticsGenerator getCegarLoopBenchmark() {
		return mCegarLoopBenchmark;
	}

	/**
	 * method called at the end of the cegar loop
	 */
	public void finish() {
		// do nothing
	}

	@Override
	protected boolean isResultUnsafe(final boolean errorGeneralizationEnabled, final Result abstractResult) {
		if (!errorGeneralizationEnabled) {
			return false;
		}
		final CFG2NestedWordAutomaton<LETTER> cFG2NestedWordAutomaton = new CFG2NestedWordAutomaton<>(mServices,
				mPref.interprocedural(), super.mCsToolkit, mPredicateFactory, mLogger);
		final INestedWordAutomaton<LETTER, IPredicate> cfg = cFG2NestedWordAutomaton
				.getNestedWordAutomaton(super.mIcfg, mStateFactoryForRefinement, super.mErrorLocs);
		return mErrorGeneralizationEngine.isResultUnsafe(abstractResult, cfg, mCsToolkit, mPredicateFactory,
				mTraceCheckAndRefinementEngine.getPredicateUnifier(), mSimplificationTechnique, mXnfConversionTechnique,
				mIcfg.getCfgSmtToolkit().getSymbolTable());
	}

	public void setWitnessAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton) {
		mWitnessAutomaton = witnessAutomaton;
	}

	private final static boolean checkStoreCounterExamples(final TAPreferences pref) {
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

	public LinkedHashSet<AbstractInterpolantAutomaton<LETTER>> getFloydHoareAutomata() {
		if (mStoreFloydHoareAutomata) {
			return mFloydHoareAutomata;
		} else {
			throw new IllegalStateException("Floyd-Hoare automata have not been stored");
		}
	}
	
	
}
