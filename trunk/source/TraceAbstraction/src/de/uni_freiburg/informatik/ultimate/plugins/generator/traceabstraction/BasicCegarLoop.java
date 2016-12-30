/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Automaton2UltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.LineCoverageCalculator;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.RefinementStrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessProductAutomaton;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * Subclass of AbstractCegarLoop which provides all algorithms for checking safety (not termination).
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public class BasicCegarLoop extends AbstractCegarLoop {
	
	protected static final int MINIMIZE_EVERY_KTH_ITERATION = 10;
	protected static final boolean REMOVE_DEAD_ENDS = true;
	protected static final boolean TRACE_HISTOGRAMM_BAILOUT = false;
	protected static final int MINIMIZATION_TIMEOUT = 1_000;
	private static final boolean NON_EA_INDUCTIVITY_CHECK = false;
	
	protected final PredicateFactoryRefinement mStateFactoryForRefinement;
	protected final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	protected final PredicateFactoryResultChecking mPredicateFactoryResultChecking;
	
	private final CegarAbsIntRunner mAbsIntRunner;
	private final InterpolantAutomatonBuilderFactory mInterpolantAutomatonBuilderFactory;
	protected final InterpolationTechnique mInterpolation;
	protected final InterpolantAutomaton mInterpolantAutomatonConstructionProcedure;
	protected final UnsatCores mUnsatCores;
	protected final boolean mUseLiveVariables;
	
	protected final boolean mComputeHoareAnnotation;
	protected final AssertCodeBlockOrder mAssertCodeBlocksIncrementally;
	
	private final boolean mDoFaultLocalizationNonFlowSensitive;
	private final boolean mDoFaultLocalizationFlowSensitive;
	private final Set<IcfgLocation> mHoareAnnotationLocations;
	
	protected final Collection<INestedWordAutomatonSimple<CodeBlock, IPredicate>> mStoredRawInterpolantAutomata;
	
	private final SearchStrategy mSearchStrategy;
	
	private final RefinementStrategyFactory mRefinementStrategyFactory;
	
	protected boolean mFallbackToFpIfInterprocedural = false;
	protected HoareAnnotationFragments mHaf;
	private INestedWordAutomatonSimple<WitnessEdge, WitnessNode> mWitnessAutomaton;
	protected IRefinementEngine<NestedWordAutomaton<CodeBlock, IPredicate>> mTraceCheckAndRefinementEngine;
	
	public BasicCegarLoop(final String name, final IIcfg<BoogieIcfgLocation> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<BoogieIcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		super(services, storage, name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs,
				services.getLoggingService().getLogger(Activator.PLUGIN_ID));
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
		// InterpolationPreferenceChecker.check(Activator.s_PLUGIN_NAME, interpolation);
		mComputeHoareAnnotation = computeHoareAnnotation;
		if (mComputeHoareAnnotation) {
			mHoareAnnotationLocations = TraceAbstractionUtils.getLocationsForWhichHoareAnnotationIsComputed(rootNode,
					mPref.getHoareAnnotationPositions());
		} else {
			mHoareAnnotationLocations = Collections.emptySet();
		}
		mHaf = new HoareAnnotationFragments(mLogger, mHoareAnnotationLocations, mPref.getHoareAnnotationPositions());
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
		
		mAbsIntRunner = new CegarAbsIntRunner(services, mCegarLoopBenchmark, rootNode, mSimplificationTechnique,
				mXnfConversionTechnique, mCsToolkit);
		mInterpolantAutomatonBuilderFactory = new InterpolantAutomatonBuilderFactory(mServices, mCsToolkit,
				mPredicateFactoryInterpolantAutomata, mIcfgContainer, mAbsIntRunner, taPrefs, mInterpolation,
				mInterpolantAutomatonConstructionProcedure, mCegarLoopBenchmark);
		
		mSearchStrategy = getSearchStrategy(prefs);
		mStoredRawInterpolantAutomata = checkStoreCounterExamples(mPref) ? new ArrayList<>() : null;
		
		final TaCheckAndRefinementPreferences taCheckAndRefinementPrefs = new TaCheckAndRefinementPreferences(mServices,
				mPref, mInterpolation, mSimplificationTechnique, mXnfConversionTechnique, mCsToolkit, mPredicateFactory,
				mIcfgContainer, mToolchainStorage, mInterpolantAutomatonBuilderFactory);
		mRefinementStrategyFactory = new RefinementStrategyFactory(mLogger, mServices, mToolchainStorage, mPref,
				taCheckAndRefinementPrefs, mAbsIntRunner, mIcfgContainer, mPredicateFactory);
	}
	
	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		final CFG2NestedWordAutomaton cFG2NestedWordAutomaton = new CFG2NestedWordAutomaton(mServices,
				mPref.interprocedural(), super.mCsToolkit, super.mPredicateFactory, mLogger);
		
		mAbstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(super.mIcfgContainer, mStateFactoryForRefinement,
				super.mErrorLocs);
		if (mComputeHoareAnnotation && mPref.getHoareAnnotationPositions() == HoareAnnotationPositions.LoopsAndPotentialCycles) {
			final INestedWordAutomaton<CodeBlock, IPredicate> nwa =
					(INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction;
			for (final IPredicate pred : nwa.getStates()) {
				for (final OutgoingCallTransition<CodeBlock, IPredicate> trans : nwa.callSuccessors(pred)) {
					mHoareAnnotationLocations.add(((ISLPredicate) pred).getProgramPoint());
					mHoareAnnotationLocations.add(((ISLPredicate) trans.getSucc()).getProgramPoint());
				}
			}
		}
		if (mWitnessAutomaton != null) {
			final WitnessProductAutomaton wpa = new WitnessProductAutomaton(mServices,
					(INestedWordAutomatonSimple<CodeBlock, IPredicate>) mAbstraction, mWitnessAutomaton, mCsToolkit,
					mPredicateFactory);
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> test =
					new RemoveUnreachable<>(new AutomataLibraryServices(mServices), wpa).getResult();
			mLogger.info("Full witness product has " + test.sizeInformation());
			mLogger.info(wpa.generateBadWitnessInformation());
			final LineCoverageCalculator origCoverage = new LineCoverageCalculator(mServices, mAbstraction);
			mAbstraction = new RemoveDeadEnds<>(new AutomataLibraryServices(mServices), wpa).getResult();
			new LineCoverageCalculator(mServices, mAbstraction, origCoverage).reportCoverage("Witness product");
		}
	}
	
	@Override
	protected boolean isAbstractionCorrect() throws AutomataOperationCanceledException {
		final INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction =
				(INestedWordAutomatonSimple<CodeBlock, IPredicate>) mAbstraction;
		mCounterexample =
				new IsEmpty<>(new AutomataLibraryServices(mServices), abstraction, mSearchStrategy).getNestedRun();
		
		if (mCounterexample == null) {
			return true;
		}
		
		if (mPref.dumpAutomata()) {
			mDumper.dumpNestedRun(mCounterexample);
		}
		mLogger.info("Found error trace");
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(mCounterexample.getWord());
		}
		final HistogramOfIterable<CodeBlock> traceHistogram = new HistogramOfIterable<>(mCounterexample.getWord());
		mCegarLoopBenchmark.reportTraceHistogramMaximum(traceHistogram.getMax());
		if (mLogger.isInfoEnabled()) {
			mLogger.info("trace histogram " + traceHistogram.toString());
		}
		if (TRACE_HISTOGRAMM_BAILOUT) {
			if (traceHistogram.getVisualizationArray()[0] > traceHistogram.getVisualizationArray().length) {
				final String message = "bailout by trace histogram " + traceHistogram.toString();
				final String taskDescription = "trying to verify (iteration " + mIteration + ")";
				throw new ToolchainCanceledException(message, getClass(), taskDescription);
			}
		}
		return false;
	}
	
	@Override
	protected LBool isCounterexampleFeasible() throws AutomataOperationCanceledException {
		
		final IRefinementStrategy strategy = mRefinementStrategyFactory.createStrategy(mCounterexample, mAbstraction,
				getIteration(), getCegarLoopBenchmark());
		try {
			mTraceCheckAndRefinementEngine = new TraceAbstractionRefinementEngine(mLogger, strategy);
		} catch (final ToolchainCanceledException tce) {
			final int traceHistogramMax = new HistogramOfIterable<>(mCounterexample.getWord()).getMax();
			final String taskDescription = "analyzing trace of length " + mCounterexample.getLength() 
				+ " with TraceHistMax " + traceHistogramMax;
			tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
			throw tce;
		}
		
		final PredicateUnifier predicateUnifier = mTraceCheckAndRefinementEngine.getPredicateUnifier();
		final LBool feasibility = mTraceCheckAndRefinementEngine.getCounterexampleFeasibility();
		
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample might be feasible");
			if (mTraceCheckAndRefinementEngine.providesICfgProgramExecution()) {
				mRcfgProgramExecution = mTraceCheckAndRefinementEngine.getIcfgProgramExecution();
			} else {
				mRcfgProgramExecution = TraceCheckerUtils.computeSomeIcfgProgramExecutionWithoutValues(mCounterexample.getWord());
			}
			
			if ((mDoFaultLocalizationNonFlowSensitive || mDoFaultLocalizationFlowSensitive)
					&& feasibility == LBool.SAT) {
				final CFG2NestedWordAutomaton cFG2NestedWordAutomaton = new CFG2NestedWordAutomaton(mServices,
						mPref.interprocedural(), super.mCsToolkit, mPredicateFactory, mLogger);
				final INestedWordAutomaton<CodeBlock, IPredicate> cfg = cFG2NestedWordAutomaton
						.getNestedWordAutomaton(super.mIcfgContainer, mStateFactoryForRefinement, super.mErrorLocs);
				final FlowSensitiveFaultLocalizer a = new FlowSensitiveFaultLocalizer(mCounterexample, cfg, mServices,
						mCsToolkit, mPredicateFactory, mCsToolkit.getModifiableGlobalsTable(), predicateUnifier,
						mDoFaultLocalizationNonFlowSensitive, mDoFaultLocalizationFlowSensitive,
						mSimplificationTechnique, mXnfConversionTechnique, mIcfgContainer.getSymboltable());
				mRcfgProgramExecution = mRcfgProgramExecution.addRelevanceInformation(a.getRelevanceInformation());
			}
		}
		
		return feasibility;
	}
	
	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		mInterpolAutomaton = mTraceCheckAndRefinementEngine.getInfeasibilityProof();
		if (NON_EA_INDUCTIVITY_CHECK) {
			final boolean inductive = new InductivityCheck(mServices, mInterpolAutomaton, false, true,
						new IncrementalHoareTripleChecker(super.mCsToolkit)).getResult();
			if (!inductive) {
				throw new AssertionError("not inductive"); 
			}
		}
		
		assert accepts(mServices, mInterpolAutomaton, mCounterexample.getWord()) : "Interpolant automaton broken!";
		assert new InductivityCheck(mServices, mInterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(super.mCsToolkit)).getResult();
	}
	
	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		final PredicateUnifier predUnifier = mTraceCheckAndRefinementEngine.getPredicateUnifier();
		return refineWithGivenAutomaton(mInterpolAutomaton, predUnifier);
	}
	
	private boolean refineWithGivenAutomaton(final NestedWordAutomaton<CodeBlock, IPredicate> inputInterpolantAutomaton,
			final PredicateUnifier predicateUnifier)
			throws AssertionError, AutomataOperationCanceledException, AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(super.mIteration);
		
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final boolean explointSigmaStarConcatOfIA = !mComputeHoareAnnotation;
		
		final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction =
				(INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction;
		
		final IHoareTripleChecker htc;
		{
			if (mTraceCheckAndRefinementEngine.getHoareTripleChecker() != null) {
				htc = mTraceCheckAndRefinementEngine.getHoareTripleChecker();
			} else {
				htc = TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
						mPref.getHoareTripleChecks(), super.mCsToolkit,
						mTraceCheckAndRefinementEngine.getPredicateUnifier());
			}
		}
		
		final InterpolantAutomatonEnhancement enhanceMode;
		if (mAbsIntRunner.hasShownInfeasibility()) {
			// Do not enhance if abstract interpretation was strong enough to prove infeasibility.
			enhanceMode = InterpolantAutomatonEnhancement.NONE;
		} else {
			enhanceMode = mPref.interpolantAutomatonEnhancement();
		}
		
		final INestedWordAutomatonSimple<CodeBlock, IPredicate> interpolantAutomaton;
		if (enhanceMode == InterpolantAutomatonEnhancement.NONE) {
			interpolantAutomaton = inputInterpolantAutomaton;
		} else {
			interpolantAutomaton = constructInterpolantAutomatonForOnDemandEnhancement(inputInterpolantAutomaton,
					predicateUnifier, htc, enhanceMode);
		}
		
		try {
			mLogger.debug("Start constructing difference");
			final PowersetDeterminizer<CodeBlock, IPredicate> psd =
					new PowersetDeterminizer<>(interpolantAutomaton, true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;
			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(mServices), oldAbstraction,
							interpolantAutomaton, psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(mServices), oldAbstraction,
							interpolantAutomaton, psd, mStateFactoryForRefinement, explointSigmaStarConcatOfIA);
				}
			} catch (final AutomataOperationCanceledException aoce) {
				final String taskDescription = "constructing difference of abstraction (" + oldAbstraction.size() + 
						"states) and interpolant automaton (currently " + interpolantAutomaton.size() + " states, " + 
						inputInterpolantAutomaton.size() + " states before enhancement)"; 
				aoce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
				throw aoce;
			} catch (final ToolchainCanceledException tce) {
				final String taskDescription = "constructing difference of abstraction (" + oldAbstraction.size() + 
						"states) and interpolant automaton (currently " + interpolantAutomaton.size() + " states, " + 
						inputInterpolantAutomaton.size() + " states before enhancement)"; 
				tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
				throw tce;
			} finally {
				if (enhanceMode != InterpolantAutomatonEnhancement.NONE) {
					assert interpolantAutomaton instanceof AbstractInterpolantAutomaton : "if enhancement is used, we need AbstractInterpolantAutomaton";
					((AbstractInterpolantAutomaton) interpolantAutomaton).switchToReadonlyMode();
				}
			}
			
			if (mPref.dumpAutomata()) {
				final String filename = "EnhancedInterpolantAutomaton_Iteration" + mIteration;
				super.writeAutomatonToFile(interpolantAutomaton, filename);
			}
			if (mAbsIntRunner.isDisabled()) {
				// check only if AI did not run
				final boolean ctxAccepted = new Accepts<>(new AutomataLibraryServices(mServices), interpolantAutomaton,
						(NestedWord<CodeBlock>) mCounterexample.getWord(), true, false).getResult();
				if (!ctxAccepted) {
					throw new AssertionError("enhanced interpolant automaton in iteration " + mIteration
							+ " broken: counterexample of length " + mCounterexample.getLength() + " not accepted");
				}
			}
			assert new InductivityCheck(mServices,
					new RemoveUnreachable<>(new AutomataLibraryServices(mServices), interpolantAutomaton).getResult(),
					false, true, new IncrementalHoareTripleChecker(super.mCsToolkit)).getResult();
			
			if (REMOVE_DEAD_ENDS) {
				if (mComputeHoareAnnotation) {
					final Difference<CodeBlock, IPredicate> difference = (Difference<CodeBlock, IPredicate>) diff;
					mHaf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
				}
				diff.removeDeadEnds();
				if (mComputeHoareAnnotation) {
					mHaf.addDeadEndDoubleDeckers(diff);
				}
			}
			mAbstraction = diff.getResult();
			
			if (mPref.dumpAutomata()) {
				final String filename = "InterpolantAutomaton_Iteration" + mIteration;
				super.writeAutomatonToFile(inputInterpolantAutomaton, filename);
			}
		} finally {
			mCegarLoopBenchmark.addEdgeCheckerData(htc.getEdgeCheckerBenchmark());
			mCegarLoopBenchmark.addPredicateUnifierData(predicateUnifier.getPredicateUnifierBenchmark());
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		}
		
		mLogger.info(predicateUnifier.collectPredicateUnifierStatistics());
		
		final Minimization minimization = mPref.getMinimization();
		switch (minimization) {
		case NONE:
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
			minimizeAbstraction(mStateFactoryForRefinement, mPredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}
		
		// MinimizeSevpa<CodeBlock, Predicate> sev = new
		// MinimizeSevpa<CodeBlock, Predicate>(abstraction);
		// new MinimizeSevpa<CodeBlock, Predicate>.Partitioning(0);
		
		// for (Predicate p : a.getStates()) {
		// assert a.numberOfOutgoingInternalTransitions(p) <= 2 : p + " has "
		// +a.numberOfOutgoingInternalTransitions(p);
		// assert a.numberOfIncomingInternalTransitions(p) <= 25 : p + " has "
		// +a.numberOfIncomingInternalTransitions(p);
		// }
		final boolean stillAccepted = new Accepts<>(new AutomataLibraryServices(mServices),
				(INestedWordAutomatonSimple<CodeBlock, IPredicate>) mAbstraction,
				(NestedWord<CodeBlock>) mCounterexample.getWord()).getResult();
		return !stillAccepted;
	}
	
	private INestedWordAutomatonSimple<CodeBlock, IPredicate> constructInterpolantAutomatonForOnDemandEnhancement(
			final NestedWordAutomaton<CodeBlock, IPredicate> inputInterpolantAutomaton,
			final PredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		final AbstractInterpolantAutomaton result;
		switch (enhanceMode) {
		case NONE:
			throw new IllegalArgumentException("In setting NONE we will not do any enhancement");
		case PREDICATE_ABSTRACTION:
		case PREDICATE_ABSTRACTION_CONSERVATIVE:
		case PREDICATE_ABSTRACTION_CANNIBALIZE: {
			final boolean conservativeSuccessorCandidateSelection =
					enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE;
			final boolean cannibalize =
					enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE;
			final DeterministicInterpolantAutomaton determinized = new DeterministicInterpolantAutomaton(mServices,
					mCsToolkit, htc, inputInterpolantAutomaton, mTraceCheckAndRefinementEngine.getPredicateUnifier(),
					conservativeSuccessorCandidateSelection, cannibalize);
			result = determinized;
		}
			break;
		case EAGER:
		case NO_SECOND_CHANCE:
		case EAGER_CONSERVATIVE: {
			final boolean conservativeSuccessorCandidateSelection =
					enhanceMode == InterpolantAutomatonEnhancement.EAGER_CONSERVATIVE;
			final boolean secondChance = enhanceMode != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE;
			final NondeterministicInterpolantAutomaton nondet =
					new NondeterministicInterpolantAutomaton(mServices, mCsToolkit, htc, inputInterpolantAutomaton,
							predicateUnifier, conservativeSuccessorCandidateSelection, secondChance);
			result = nondet;
		}
			break;
		default:
			throw new UnsupportedOperationException("unknown " + enhanceMode);
		}
		return result;
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
					mIcfgContainer.getIdentifier() + "_DiffAutomatonBeforeMinimization_Iteration" + mIteration;
			super.writeAutomatonToFile(mAbstraction, filename);
		}
		final Function<ISLPredicate, BoogieIcfgLocation> lcsProvider = x -> x.getProgramPoint();
		AutomataMinimization<BoogieIcfgLocation, ISLPredicate> am;
		try {
			am = new AutomataMinimization<>(mServices, (INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction,
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
			final IDoubleDeckerAutomaton<CodeBlock, IPredicate> newAbstraction = am.getMinimizedAutomaton();
			
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
		final INestedWordAutomaton<CodeBlock, IPredicate> abstraction =
				(INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction;
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.HoareAnnotationTime.toString());
		new HoareAnnotationExtractor(mServices, abstraction, mHaf);
		final HoareAnnotationComposer clha = new HoareAnnotationComposer(mIcfgContainer, mCsToolkit, mPredicateFactory,
				mHaf, mServices, mSimplificationTechnique, mXnfConversionTechnique);
		final HoareAnnotationWriter writer = new HoareAnnotationWriter(mIcfgContainer, mCsToolkit, mPredicateFactory,
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
				return mIcfgContainer;
			}
			try {
				return Automaton2UltimateModel.ultimateModel(new AutomataLibraryServices(mServices),
						mArtifactAutomaton);
			} catch (final AutomataOperationCanceledException e) {
				return null;
			}
		} else if (mPref.artifact() == Artifact.RCFG) {
			return mIcfgContainer;
		} else {
			throw new IllegalArgumentException();
		}
	}
	
	protected static boolean accepts(final IUltimateServiceProvider services,
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> nia, final Word<CodeBlock> word)
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
	
	public void setWitnessAutomaton(final INestedWordAutomatonSimple<WitnessEdge, WitnessNode> witnessAutomaton) {
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
}
