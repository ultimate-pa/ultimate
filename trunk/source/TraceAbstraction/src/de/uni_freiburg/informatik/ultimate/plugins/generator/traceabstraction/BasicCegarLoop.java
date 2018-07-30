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

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
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
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.EpsilonNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty.SearchStrategy;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.DangerInvariantResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.SubtaskFileIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram.PathProgramConstructionResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgAngelicProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization.FlowSensitiveFaultLocalizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.InterpolantAutomatonBuilderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.DangerInvariantGuesser;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.CounterexampleSearchStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier.CoverageRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.BaseRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.RefinementStrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.interactive.InteractiveRefinementStrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessUtils.Property;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
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
	protected static final int MINIMIZATION_TIMEOUT = 1_000;
	private static final boolean NON_EA_INDUCTIVITY_CHECK = false;

	/**
	 * If the trace histogram max is larger than this number we try to find a danger invariant. Only used for debugging.
	 */
	private static final int DEBUG_DANGER_INVARIANTS_THRESHOLD = Integer.MAX_VALUE;

	protected final PredicateFactoryRefinement mStateFactoryForRefinement;
	protected final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	protected final PredicateFactoryResultChecking mPredicateFactoryResultChecking;

	private final InterpolantAutomatonBuilderFactory<LETTER> mInterpolantAutomatonBuilderFactory;
	protected final InterpolationTechnique mInterpolation;
	protected final InterpolantAutomaton mInterpolantAutomatonConstructionProcedure;
	protected final UnsatCores mUnsatCores;
	protected final boolean mUseLiveVariables;

	protected final boolean mComputeHoareAnnotation;
	protected final AssertCodeBlockOrder mAssertCodeBlocksIncrementally;

	private final RelevanceAnalysisMode mFaultLocalizationMode;
	private final boolean mFaultLocalizationAngelic;
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
	private final boolean mStoreFloydHoareAutomata;
	private final LinkedHashSet<Pair<AbstractInterpolantAutomaton<LETTER>, IPredicateUnifier>> mFloydHoareAutomata =
			new LinkedHashSet<>();
	protected final TaskIdentifier mTaskIdentifier;
	private boolean mFirstReuseDump = true;
	private static final boolean DUMP_DIFFICULT_PATH_PROGRAMS = false;

	public BasicCegarLoop(final DebugIdentifier name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		super(services, storage, name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs,
				services.getLoggingService().getLogger(Activator.PLUGIN_ID));
		// TODO: TaskIdentifier should probably be provided by caller
		mTaskIdentifier = new SubtaskFileIdentifier(null, mIcfg.getIdentifier() + "_" + name);
		mPathProgramDumpController = new PathProgramDumpController<>(mServices, mPref, mIcfg);
		if (mFallbackToFpIfInterprocedural && rootNode.getProcedureEntryNodes().size() > 1) {
			if (interpolation == InterpolationTechnique.FPandBP) {
				mLogger.info("fallback from FPandBP to FP because CFG is interprocedural");
				mInterpolation = InterpolationTechnique.ForwardPredicates;
			} else {
				mInterpolation = interpolation;
			}
		} else {
			mInterpolation = interpolation;
		}
		mInterpolantAutomatonConstructionProcedure = mPref.interpolantAutomaton();
		mComputeHoareAnnotation = computeHoareAnnotation;
		if (mComputeHoareAnnotation) {
			mHoareAnnotationLocations = (Set<IcfgLocation>) TraceAbstractionUtils
					.getLocationsForWhichHoareAnnotationIsComputed(rootNode, mPref.getHoareAnnotationPositions());
		} else {
			mHoareAnnotationLocations = Collections.emptySet();
		}
		mStoreFloydHoareAutomata = taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE;
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
		mFaultLocalizationMode =
				prefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS_MODE,
						RelevanceAnalysisMode.class);
		mFaultLocalizationAngelic =
				prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_ERROR_TRACE_ANGELIC_VERIFICATION_ACTIVE);

		final PathProgramCache<LETTER> pathProgramCache = new PathProgramCache<>(mLogger);
		final CegarAbsIntRunner<LETTER> absIntRunner = new CegarAbsIntRunner<>(services, mCegarLoopBenchmark, rootNode,
				mSimplificationTechnique, mXnfConversionTechnique, mCsToolkit, pathProgramCache, taPrefs);
		mInterpolantAutomatonBuilderFactory = new InterpolantAutomatonBuilderFactory<>(mServices, mCsToolkit,
				mPredicateFactoryInterpolantAutomata, mIcfg, absIntRunner, taPrefs, mInterpolation,
				mInterpolantAutomatonConstructionProcedure, mCegarLoopBenchmark);

		mSearchStrategy = getSearchStrategy(prefs);
		mStoredRawInterpolantAutomata = checkStoreCounterExamples(mPref) ? new ArrayList<>() : null;

		final TaCheckAndRefinementPreferences<LETTER> taCheckAndRefinementPrefs = new TaCheckAndRefinementPreferences<>(
				mServices, mPref, mInterpolation, mSimplificationTechnique, mXnfConversionTechnique, mCsToolkit,
				mPredicateFactory, mIcfg, mToolchainStorage, mInterpolantAutomatonBuilderFactory);

		if (mInteractive.isInteractiveMode()) {
			mRefinementStrategyFactory =
					new InteractiveRefinementStrategyFactory<>(mLogger, mServices, mToolchainStorage, mInteractive,
							mPref, taCheckAndRefinementPrefs, absIntRunner, mIcfg, mPredicateFactory, pathProgramCache);
		} else {
			mRefinementStrategyFactory = new RefinementStrategyFactory<>(mLogger, mServices, mToolchainStorage, mPref,
					taCheckAndRefinementPrefs, absIntRunner, mIcfg, mPredicateFactory, pathProgramCache);
		}

		if (mPref.dumpOnlyReuseAutomata()) {
			// Construct an empty file. We need this empty file in cases where
			// the CFG does not have error location and no automaton is dumped.
			mLogger.info("Dumping reuse automata for " + mTaskIdentifier.toString());
			final String filename = mTaskIdentifier + "-reuse";
			final String fullPath =
					mPref.dumpPath() + File.separator + filename + "." + mPrintAutomataLabeling.getFileEnding();
			final File file = new File(fullPath);
			try {
				final FileWriter fw = new FileWriter(file, false);
				fw.close();
			} catch (final IOException e) {
				if (mLogger.isErrorEnabled()) {
					mLogger.error("Creating FileWriter did not work.", e);
				}
			}
		}
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		mAbstraction = CFG2NestedWordAutomaton.constructAutomatonWithSPredicates(mServices, super.mIcfg,
				mStateFactoryForRefinement, super.mErrorLocs, mPref.interprocedural(), mPredicateFactory);

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
			mAbstraction = WitnessUtils.constructIcfgAndWitnessProduct(mServices, mAbstraction, mWitnessAutomaton,
					mCsToolkit, mPredicateFactory, mStateFactoryForRefinement, mLogger, Property.NON_REACHABILITY);
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
			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.DUMP_TIME);
			mDumper.dumpNestedRun(mCounterexample);
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DUMP_TIME);
		}
		mLogger.info("Found error trace");

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(mCounterexample.getWord());
		}
		final HistogramOfIterable<LETTER> traceHistogram = new HistogramOfIterable<>(mCounterexample.getWord());
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

		// Don't send the histogram: the complete run is sent already.
		// mInteractive.send(traceHistogram);
		return false;
	}

	private void checkForDangerInvariantAndReport() {
		final Set<? extends IcfgEdge> allowedTransitions = PathInvariantsGenerator.extractTransitionsFromRun(
				(NestedRun<? extends IAction, IPredicate>) mCounterexample,
				mIcfg.getCfgSmtToolkit().getIcfgEdgeFactory());
		final PathProgramConstructionResult ppResult =
				PathProgram.constructPathProgram("PathInvariantsPathProgram", mIcfg, allowedTransitions);
		final IIcfg<IcfgLocation> pathProgram = ppResult.getPathProgram();
		final PredicateFactory predicateFactory = mPredicateFactory;
		final IPredicateUnifier predicateUnifier = new PredicateUnifier(mServices, mCsToolkit.getManagedScript(),
				predicateFactory, mCsToolkit.getSymbolTable(), SimplificationTechnique.SIMPLIFY_DDA,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final IPredicate precondition = predicateUnifier.getTruePredicate();
		final DangerInvariantGuesser dig = new DangerInvariantGuesser(pathProgram, mServices, mToolchainStorage,
				precondition, predicateFactory, predicateUnifier, mCsToolkit);
		final boolean hasDangerInvariant = dig.isDangerInvariant();
		if (hasDangerInvariant) {
			final Map<IcfgLocation, IPredicate> invar = dig.getCandidateInvariant();
			final Set<IcfgLocation> errorLocations = IcfgUtils.getErrorLocations(pathProgram);
			final DangerInvariantResult<?, IPredicate> res = new DangerInvariantResult<>(Activator.PLUGIN_ID, invar,
					errorLocations, mServices.getBacktranslationService());
			mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
		}
	}

	@Override
	protected LBool isCounterexampleFeasible() throws AutomataOperationCanceledException {

		final BaseRefinementStrategy<LETTER> strategy = mRefinementStrategyFactory.createStrategy(mCounterexample,
				mAbstraction, new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()), mPredicateFactoryInterpolantAutomata);
		try {
			if (mPref.hasLimitPathProgramCount() && mPref.getLimitPathProgramCount() < mRefinementStrategyFactory
					.getPathProgramCache().getPathProgramCount(mCounterexample)) {
				final String taskDescription = "bailout by path program count limit in iteration " + mIteration;
				throw new TaskCanceledException(UserDefinedLimit.PATH_PROGRAM_ATTEMPTS, getClass(), taskDescription);
			}

			mTraceCheckAndRefinementEngine = new TraceAbstractionRefinementEngine<>(mLogger, strategy);
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
						TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(mCounterexample.getWord());
			}

			if (mFaultLocalizationMode != RelevanceAnalysisMode.NONE && feasibility == LBool.SAT) {
				final INestedWordAutomaton<LETTER, IPredicate> cfg = CFG2NestedWordAutomaton
						.constructAutomatonWithSPredicates(mServices, super.mIcfg, mStateFactoryForRefinement,
								super.mErrorLocs, mPref.interprocedural(), mPredicateFactory);
				final FlowSensitiveFaultLocalizer<LETTER> fl = new FlowSensitiveFaultLocalizer<>(
						(NestedRun<LETTER, IPredicate>) mCounterexample, cfg, mServices, mCsToolkit, mPredicateFactory,
						mCsToolkit.getModifiableGlobalsTable(), predicateUnifier, mFaultLocalizationMode,
						mSimplificationTechnique, mXnfConversionTechnique, mIcfg.getCfgSmtToolkit().getSymbolTable(),
						(IIcfg<IcfgLocation>) mIcfg);
				if (mRcfgProgramExecution instanceof IcfgProgramExecution) {
					mRcfgProgramExecution = ((IcfgProgramExecution) mRcfgProgramExecution)
							.addRelevanceInformation(fl.getRelevanceInformation());
				} else {
					throw new UnsupportedOperationException("Program execution is not " + IcfgProgramExecution.class);
				}

				if (mFaultLocalizationAngelic) {
					mRcfgProgramExecution =
							new IcfgAngelicProgramExecution(mRcfgProgramExecution, fl.getAngelicStatus());
				}
			}
		} else {
			if (DUMP_DIFFICULT_PATH_PROGRAMS) {
				mPathProgramDumpController.reportPathProgram((NestedRun<LETTER, IPredicate>) mCounterexample,
						((TraceAbstractionRefinementEngine<LETTER>) mTraceCheckAndRefinementEngine)
								.somePerfectSequenceFound(),
						mIteration);
			}
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
					new IncrementalHoareTripleChecker(super.mCsToolkit, false)).getResult();

			if (!inductive) {
				throw new AssertionError("not inductive");
			}
		}

		assert accepts(mServices, mInterpolAutomaton, mCounterexample.getWord()) : "Interpolant automaton broken!";
		assert new InductivityCheck<>(mServices, mInterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(super.mCsToolkit, false)).getResult();
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
					mFloydHoareAutomata.add(new Pair<>(ia, predicateUnifier));
				}
			}
		}

		// TODO: HTC and predicateunifier statistics are saved in the following method, but it seems better to save them
		// at the end of the htc lifecycle instead of there
		computeAutomataDifference(minuend, subtrahend, subtrahendBeforeEnhancement, predicateUnifier,
				exploitSigmaStarConcatOfIa, htc, enhanceMode, useErrorAutomaton, automatonType);

		mLogger.info(predicateUnifier.collectPredicateUnifierStatistics());

		minimizeAbstractionIfEnabled();

		final boolean stillAccepted = new Accepts<>(new AutomataLibraryServices(mServices),
				(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction,
				(NestedWord<LETTER>) mCounterexample.getWord()).getResult();
		return !stillAccepted;
	}

	/**
	 *
	 * @return true iff all traces of the path program defined by the counterexample of this iteration were subtracted
	 *         from the abstraction
	 */
	private boolean checkPathProgramRemoval()
			throws AutomataLibraryException, AutomataOperationCanceledException, AssertionError {
		final boolean pathProgramShouldHaveBeenRemoved = mTraceCheckAndRefinementEngine.somePerfectSequenceFound()
				&& mPref.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NONE;
		if (!pathProgramShouldHaveBeenRemoved) {
			return true;
		}
		final Set<LETTER> counterexampleLetters = mCounterexample.getWord().asSet();
		final PathProgramConstructionResult ppcr = PathProgram
				.constructPathProgram("PathprogramSubtractedCheckIteration" + mIteration, mIcfg, counterexampleLetters);
		final Map<IIcfgTransition<?>, IIcfgTransition<?>> oldTransition2NewTransition =
				ppcr.getOldTransition2NewTransition();
		final Map<IIcfgTransition<?>, IIcfgTransition<?>> newTransition2OldTransition =
				DataStructureUtils.constructReverseMapping(oldTransition2NewTransition);
		final Map<IcfgLocation, IcfgLocation> oldLocation2NewLocation = ppcr.getLocationMapping();
		final PathProgram pp = ppcr.getPathProgram();
		final IcfgLocation errorLoc =
				((ISLPredicate) mCounterexample.getStateSequence().get(mCounterexample.getStateSequence().size() - 1))
						.getProgramPoint();
		final VpAlphabet<LETTER> newVpAlphabet =
				CFG2NestedWordAutomaton.extractVpAlphabet(mIcfg, !mPref.interprocedural());
		final VpAlphabet<LETTER> oldVpAlphabet =
				new VpAlphabet<>(newVpAlphabet, (Map<LETTER, LETTER>) newTransition2OldTransition);
		final INestedWordAutomaton<LETTER, IPredicate> pathProgramAutomaton =
				CFG2NestedWordAutomaton.constructAutomatonWithDebugPredicates(mServices, pp,
						mPredicateFactoryResultChecking, Collections.singleton(oldLocation2NewLocation.get(errorLoc)),
						mPref.interprocedural(), newVpAlphabet, newTransition2OldTransition);
		assert pathProgramAutomaton.getFinalStates().size() == 1 : "incorrect accepting states";
		final INestedWordAutomaton<LETTER, IPredicate> intersection =
				new Intersect<>(new AutomataLibraryServices(mServices), mPredicateFactoryResultChecking,
						(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction,
						pathProgramAutomaton).getResult();
		final Boolean isEmpty = new IsEmpty<>(new AutomataLibraryServices(mServices), intersection).getResult();
		return isEmpty;
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
				final INestedWordAutomaton<LETTER, IPredicate> cfg = CFG2NestedWordAutomaton
						.constructAutomatonWithSPredicates(mServices, super.mIcfg, mStateFactoryForRefinement,
								super.mErrorLocs, mPref.interprocedural(), mPredicateFactory);
				mErrorGeneralizationEngine.faultLocalizationWithStorage(cfg, mCsToolkit, mPredicateFactory,
						mTraceCheckAndRefinementEngine.getPredicateUnifier(), mSimplificationTechnique,
						mXnfConversionTechnique, mIcfg.getCfgSmtToolkit().getSymbolTable(), null,
						(NestedRun<LETTER, IPredicate>) mCounterexample, (IIcfg<IcfgLocation>) mIcfg);
			}

			dumpAutomatonIfEnabled(subtrahend, "Enhanced", automatonType);
			dumpOrAppendAutomatonForReuseIfEnabled(subtrahend, predicateUnifier);

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

			dumpAutomatonIfEnabled(subtrahendBeforeEnhancement, "Original", automatonType);

		} finally

		{
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

	protected void dumpOrAppendAutomatonForReuseIfEnabled(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> automaton,
			final IPredicateUnifier predicateUnifier) {
		if (mPref.dumpOnlyReuseAutomata()) {

			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.DUMP_TIME);
			mLogger.info("Dumping reuse automata for " + mTaskIdentifier.toString() + " " + automaton.getClass());
			final String filename = mTaskIdentifier + "-reuse";
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> printedAutomaton;
			final AutomataLibraryServices services = new AutomataLibraryServices(mServices);
			final boolean addPredicateImplicationInformation = true;
			if (addPredicateImplicationInformation) {
				final HashRelation<IPredicate, IPredicate> outgoingEpsilonTransitions =
						((CoverageRelation) predicateUnifier.getCoverageRelation()).getCopyOfImplicationRelation();
				INestedWordAutomaton<LETTER, IPredicate> backingNestedWordAutomaton;
				try {
					backingNestedWordAutomaton = new RemoveDeadEnds<>(services, automaton).getResult();
					if (backingNestedWordAutomaton.getStates().isEmpty()) {
						mLogger.warn("Automaton with emtpy language -- ommited dump");
						mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DUMP_TIME);
						return;
					}
				} catch (final AutomataOperationCanceledException e) {
					throw new AssertionError(e);
				}
				printedAutomaton =
						new EpsilonNestedWordAutomaton<>(backingNestedWordAutomaton, outgoingEpsilonTransitions);
			} else {
				printedAutomaton = automaton;
			}
			new AutomatonDefinitionPrinter<String, String>(services, "nwa" + mIteration,
					mPref.dumpPath() + File.separator + filename, mPrintAutomataLabeling, "", !mFirstReuseDump,
					printedAutomaton);
			mFirstReuseDump = false;
			mLogger.info("Finished dumping");
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DUMP_TIME);
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
				false, true, new IncrementalHoareTripleChecker(super.mCsToolkit, false)).getResult();
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

	protected AbstractInterpolantAutomaton<LETTER> constructInterpolantAutomatonForOnDemandEnhancement(
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
					predicateUnifier, htc, enhanceMode);
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
					final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
					final InterpolantAutomatonEnhancement enhanceMode) {
		final boolean conservativeSuccessorCandidateSelection =
				enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE;
		final boolean cannibalize = enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE;
		return new DeterministicInterpolantAutomaton<>(mServices, mCsToolkit, htc, inputInterpolantAutomaton,
				predicateUnifier, conservativeSuccessorCandidateSelection, cannibalize);
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
			final String filename = mIcfg.getIdentifier() + "_DiffAutomatonBeforeMinimization_Iteration" + mIteration;
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
		final HoareAnnotationWriter writer = new HoareAnnotationWriter(mIcfg, mCsToolkit, mPredicateFactory, clha,
				mServices, mSimplificationTechnique, mXnfConversionTechnique);
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
		final INestedWordAutomaton<LETTER, IPredicate> cfg =
				CFG2NestedWordAutomaton.constructAutomatonWithSPredicates(mServices, super.mIcfg,
						mStateFactoryForRefinement, super.mErrorLocs, mPref.interprocedural(), mPredicateFactory);
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

	public LinkedHashSet<Pair<AbstractInterpolantAutomaton<LETTER>, IPredicateUnifier>> getFloydHoareAutomata() {
		if (mStoreFloydHoareAutomata) {
			return mFloydHoareAutomata;
		}
		throw new IllegalStateException("Floyd-Hoare automata have not been stored");
	}
}
