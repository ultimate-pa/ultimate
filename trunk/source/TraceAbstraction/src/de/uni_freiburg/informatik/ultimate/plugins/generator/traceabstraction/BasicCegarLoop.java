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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.AStarHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.IHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantSleepSetOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetDelayReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetNewStateReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetVisitorAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.UnionIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.LazyPetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.DangerInvariantResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrderType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier.ScoringMethod;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram.PathProgramConstructionResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgAngelicProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.SleepSetStateFactoryForRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization.FlowSensitiveFaultLocalizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SyntacticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.ThreadSeparatingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.PathInvariantsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.DangerInvariantGuesser;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.CounterexampleSearchStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessUtils.Property;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * Subclass of AbstractCegarLoop which provides all algorithms for checking safety (not termination).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class BasicCegarLoop<L extends IIcfgTransition<?>> extends AbstractCegarLoop<L> {

	public enum AutomatonType {
		FLOYD_HOARE, ERROR;

		private String mLongString;

		static {
			FLOYD_HOARE.mLongString = "FloydHoare";
			ERROR.mLongString = "Error";
		}

		private String mShortString;

		static {
			FLOYD_HOARE.mShortString = "Fh";
			ERROR.mShortString = "Err";
		}

		public String getLongString() {
			return mLongString;
		}

		public String getShortString() {
			return mShortString;
		}

	}

	public enum PetriNetLbe {

		OFF,
		/**
		 * TODO: documentation
		 */
		SEMANTIC_BASED_MOVER_CHECK,
		/**
		 * TODO: documentation
		 */
		VARIABLE_BASED_MOVER_CHECK,
	}

	/**
	 * Indicates a kind of partial order reduction.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 */
	public enum PartialOrderMode {
		/**
		 * No partial order reduction is performed.
		 */
		NONE,
		/**
		 * Sleep set partial order reduction. Delay sets are used to handle loops, and the reduced automaton is a
		 * sub-structure of the input.
		 */
		SLEEP_DELAY_SET,
		/**
		 * Sleep set partial order reduction. Unrolling and splitting is performed to achieve a minimal reduction (in
		 * terms of the language). This duplicates states of the input automaton.
		 */
		SLEEP_NEW_STATES
	}

	protected static final int MINIMIZE_EVERY_KTH_ITERATION = 10;
	protected static final boolean REMOVE_DEAD_ENDS = true;
	protected static final int MINIMIZATION_TIMEOUT = 1_000;
	private static final boolean NON_EA_INDUCTIVITY_CHECK = false;

	/**
	 * If the trace histogram max is larger than this number we try to find a danger invariant. Only used for debugging.
	 */
	private static final int DEBUG_DANGER_INVARIANTS_THRESHOLD = Integer.MAX_VALUE;
	private static final boolean DUMP_DIFFICULT_PATH_PROGRAMS = false;

	protected final PredicateFactoryRefinement mStateFactoryForRefinement;
	protected final SleepSetStateFactoryForRefinement<L> mSleepSetStateFactory;
	protected final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	protected final PredicateFactoryResultChecking mPredicateFactoryResultChecking;

	protected final InterpolationTechnique mInterpolation;
	protected final InterpolantAutomaton mInterpolantAutomatonConstructionProcedure;
	protected final UnsatCores mUnsatCores;
	protected final boolean mUseLiveVariables;

	protected final boolean mComputeHoareAnnotation;
	protected final AssertCodeBlockOrderType mAssertCodeBlocksIncrementally;
	protected final Collection<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mStoredRawInterpolantAutomata;

	private final RelevanceAnalysisMode mFaultLocalizationMode;
	private final boolean mFaultLocalizationAngelic;
	private final Set<IcfgLocation> mHoareAnnotationLocations;
	private final SearchStrategy mSearchStrategy;
	private final StrategyFactory<L> mStrategyFactory;
	private final PathProgramDumpController<L> mPathProgramDumpController;
	private final ErrorGeneralizationEngine<L> mErrorGeneralizationEngine;
	private final boolean mStoreFloydHoareAutomata;
	private final LinkedHashSet<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> mFloydHoareAutomata =
			new LinkedHashSet<>();

	protected boolean mFallbackToFpIfInterprocedural = false;
	protected HoareAnnotationFragments<L> mHaf;
	protected IRefinementEngine<L, NestedWordAutomaton<L, IPredicate>> mRefinementEngine;

	private INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> mWitnessAutomaton;
	private boolean mFirstReuseDump = true;
	private boolean mUseHeuristicEmptinessCheck = false;
	private final ScoringMethod mScoringMethod;
	private final AStarHeuristic mAStarHeuristic;
	private final Integer mAStarRandomHeuristicSeed;

	protected final IPLBECompositionFactory<L> mCompositionFactory;

	public BasicCegarLoop(final DebugIdentifier name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> transitionClazz) {
		super(services, name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs,
				services.getLoggingService().getLogger(Activator.PLUGIN_ID), transitionClazz);
		mPathProgramDumpController = new PathProgramDumpController<>(mServices, mPref, mIcfg);
		mCompositionFactory = compositionFactory;
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
				predicateFactory, computeHoareAnnotation, mHoareAnnotationLocations);
		mSleepSetStateFactory = new SleepSetStateFactoryForRefinement<>(predicateFactory);
		mPredicateFactoryInterpolantAutomata = new PredicateFactoryForInterpolantAutomata(
				super.mCsToolkit.getManagedScript(), mPredicateFactory, computeHoareAnnotation);

		mAssertCodeBlocksIncrementally = mServices.getPreferenceProvider(Activator.PLUGIN_ID).getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY,
				AssertCodeBlockOrderType.class);

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

		mSearchStrategy = getSearchStrategy(prefs);
		mStoredRawInterpolantAutomata = checkStoreCounterExamples(mPref) ? new ArrayList<>() : null;

		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs =
				new TaCheckAndRefinementPreferences<>(mServices, mPref, mInterpolation, mSimplificationTechnique,
						mXnfConversionTechnique, mCsToolkit, mPredicateFactory, mIcfg);

		mStrategyFactory = new StrategyFactory<>(mLogger, mServices, mPref, taCheckAndRefinementPrefs, mIcfg,
				mPredicateFactory, mPredicateFactoryInterpolantAutomata, mTransitionClazz);

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
		// Heuristic Emptiness Check
		mUseHeuristicEmptinessCheck = taPrefs.useHeuristicEmptinessCheck();
		mScoringMethod = taPrefs.getHeuristicEmptinessCheckScoringMethod();
		mAStarHeuristic = taPrefs.getHeuristicEmptinessCheckAStarHeuristic();
		mAStarRandomHeuristicSeed = taPrefs.getHeuristicEmptinessCheckAStarHeuristicRandomSeed();
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		if (isSequential()) {
			mAbstraction = CFG2NestedWordAutomaton.constructAutomatonWithSPredicates(mServices, super.mIcfg,
					mStateFactoryForRefinement, super.mErrorLocs, mPref.interprocedural(), mPredicateFactory);
		} else {
			final boolean addThreadUsageMonitors = true;
			final BoundedPetriNet<L, IPredicate> petrifiedCfg =
					CFG2NestedWordAutomaton.constructPetriNetWithSPredicates(mServices, mIcfg,
							mStateFactoryForRefinement, mErrorLocs, false, mPredicateFactory, addThreadUsageMonitors);
			final BoundedPetriNet<L, IPredicate> net;
			if (mPref.useLbeInConcurrentAnalysis() != PetriNetLbe.OFF) {
				final PetriNetLargeBlockEncoding<L> lbe =
						new PetriNetLargeBlockEncoding<>(mServices, mIcfg.getCfgSmtToolkit(), petrifiedCfg,
								mPref.useLbeInConcurrentAnalysis(), mCompositionFactory, mTransitionClazz);
				final BoundedPetriNet<L, IPredicate> lbecfg = lbe.getResult();
				mServices.getBacktranslationService().addTranslator(lbe.getBacktranslator());
				net = lbecfg;
				mServices.getResultService().reportResult(Activator.PLUGIN_ID, new StatisticsResult<>(
						Activator.PLUGIN_NAME, "PetriNetLargeBlockEncoding benchmarks", lbe.getStatistics()));
			} else {
				net = petrifiedCfg;
			}

			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton;
			if (mPref.getPartialOrderMode() != PartialOrderMode.NONE) {
				// Partial Order reductions aim to avoid the explicit construction of the full finite automaton.
				automaton = new LazyPetriNet2FiniteAutomaton<>(mStateFactoryForRefinement, net,
						new AutomataLibraryServices(mServices));
			} else {
				try {
					automaton = new PetriNet2FiniteAutomaton<>(new AutomataLibraryServices(mServices),
							mStateFactoryForRefinement, net).getResult();
				} catch (final PetriNetNot1SafeException e) {
					final Collection<?> unsafePlaces = e.getUnsafePlaces();
					if (unsafePlaces == null) {
						throw new AssertionError("Unable to find Petri net place that violates 1-safety");
					}
					final ISLPredicate unsafePlace = (ISLPredicate) unsafePlaces.iterator().next();
					final String proc = unsafePlace.getProgramPoint().getProcedure();
					throw new IllegalStateException(
							"Petrification does not provide enough thread instances for " + proc);
				}
			}
			mAbstraction = computePartialOrderReduction(mPref.getPartialOrderMode(), automaton);
		}

		if (mComputeHoareAnnotation
				&& mPref.getHoareAnnotationPositions() == HoareAnnotationPositions.LoopsAndPotentialCycles) {
			final INestedWordAutomaton<L, IPredicate> nwa = (INestedWordAutomaton<L, IPredicate>) mAbstraction;
			for (final IPredicate pred : nwa.getStates()) {
				for (final OutgoingCallTransition<L, IPredicate> trans : nwa.callSuccessors(pred)) {
					mHoareAnnotationLocations.add(((ISLPredicate) pred).getProgramPoint());
					mHoareAnnotationLocations.add(((ISLPredicate) trans.getSucc()).getProgramPoint());
				}
			}
		}
		if (mWitnessAutomaton != null) {
			mAbstraction = WitnessUtils.constructIcfgAndWitnessProduct(mServices, mAbstraction, mWitnessAutomaton,
					mCsToolkit, mPredicateFactory, mStateFactoryForRefinement, mLogger, Property.NON_REACHABILITY);
		}
	}

	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> computePartialOrderReduction(
			final PartialOrderMode mode, final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> input)
			throws AutomataOperationCanceledException {
		if (mode == PartialOrderMode.NONE) {
			return input;
		}

		final IIndependenceRelation<IPredicate, L> indep = new ThreadSeparatingIndependenceRelation<>(
				new CachedIndependenceRelation<>(new UnionIndependenceRelation<>(Arrays.asList(
						new SyntacticIndependenceRelation<>(),
						new SemanticIndependenceRelation<>(mServices, mCsToolkit.getManagedScript(), false, true)))));
		final ISleepSetOrder<IPredicate, L> order =
				new ConstantSleepSetOrder<>(input.getVpAlphabet().getInternalAlphabet());

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.PartialOrderReductionTime);
		final AutomataLibraryServices automataServices = new AutomataLibraryServices(mServices);
		final SleepSetVisitorAutomaton<L, IPredicate> automatonConstructor;
		switch (mode) {
		case SLEEP_DELAY_SET:
			automatonConstructor = new SleepSetVisitorAutomaton<>(input, automataServices, mStateFactoryForRefinement);
			new SleepSetDelayReduction<>(automataServices, input, indep, order, automatonConstructor);
			break;
		case SLEEP_NEW_STATES:
			automatonConstructor =
					new SleepSetVisitorAutomaton<>(x -> input.isInitial(mSleepSetStateFactory.getOriginalState(x)),
							x -> input.isFinal(mSleepSetStateFactory.getOriginalState(x)), input.getVpAlphabet(),
							automataServices, mStateFactoryForRefinement);
			new SleepSetNewStateReduction<>(automataServices, input, indep, order, mSleepSetStateFactory,
					automatonConstructor);
			break;
		default:
			throw new UnsupportedOperationException("Unsupported POR mode: " + mode);
		}
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> result =
				automatonConstructor.getReductionAutomaton();
		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.PartialOrderReductionTime);

		mLogger.warn("Sleep set: input automaton " + input.sizeInformation());
		mLogger.warn("Sleep set: output automaton " + result.sizeInformation());

		final StatisticsData data = new StatisticsData();
		data.aggregateBenchmarkData(indep.getStatistics());
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new StatisticsResult<>(Activator.PLUGIN_NAME, "Independence relation benchmarks", data));

		return result;
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction =
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction;

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.EmptinessCheckTime);
		if (mUseHeuristicEmptinessCheck) {
			mCounterexample = new IsEmptyHeuristic<>(new AutomataLibraryServices(mServices), abstraction,
					IHeuristic.getHeuristic(mAStarHeuristic, mScoringMethod, mAStarRandomHeuristicSeed)).getNestedRun();

			assert checkIsEmptyHeuristic(abstraction) : "IsEmptyHeuristic did not match IsEmpty";
		} else {
			mCounterexample =
					new IsEmpty<>(new AutomataLibraryServices(mServices), abstraction, mSearchStrategy).getNestedRun();
		}
		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.EmptinessCheckTime);

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
				new IsEmpty<>(new AutomataLibraryServices(mServices), abstraction, mSearchStrategy).getNestedRun();

		final Function<NestedRun<L, IPredicate>, String> toStr =
				a -> a.getWord().asList().stream().map(b -> "T" + b.hashCode()).collect(Collectors.joining(" "));

		if (isEmptyHeuristicCex == null && isEmptyCex == null) {
			return true;
		} else if (isEmptyHeuristicCex != null && isEmptyCex == null) {
			mLogger.fatal("IsEmptyHeuristic found a path but IsEmpty did not.");
			mLogger.fatal("IsEmptyHeuristic: " + toStr.apply(isEmptyHeuristicCex));
			return false;
		} else if (isEmptyHeuristicCex == null && isEmptyCex != null) {
			mLogger.fatal("IsEmptyHeuristic found no path but IsEmpty did.");
			mLogger.fatal("IsEmpty         : " + toStr.apply(isEmptyCex));
			return false;
		} else if (isEmptyHeuristicCex != null && isEmptyCex != null) {
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
		final IPredicateUnifier predicateUnifier = new PredicateUnifier(mLogger, mServices,
				mCsToolkit.getManagedScript(), predicateFactory, mCsToolkit.getSymbolTable(),
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final IPredicate precondition = predicateUnifier.getTruePredicate();
		final DangerInvariantGuesser dig = new DangerInvariantGuesser(pathProgram, mServices, precondition,
				predicateFactory, predicateUnifier, mCsToolkit);
		final boolean hasDangerInvariant = dig.isDangerInvariant();
		if (hasDangerInvariant) {
			final Map<IcfgLocation, IPredicate> invarP = dig.getCandidateInvariant();
			final Map<IcfgLocation, Term> invarT =
					invarP.entrySet().stream().collect(Collectors.toMap(Entry::getKey, x -> x.getValue().getFormula()));
			final Set<IcfgLocation> errorLocations = IcfgUtils.getErrorLocations(pathProgram);
			final DangerInvariantResult<?, Term> res = new DangerInvariantResult<>(Activator.PLUGIN_ID, invarT,
					errorLocations, mServices.getBacktranslationService());
			mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
		}
		return hasDangerInvariant;
	}

	@Override
	protected LBool isCounterexampleFeasible() throws AutomataOperationCanceledException {

		try {
			if (mPref.hasLimitPathProgramCount() && mPref.getLimitPathProgramCount() < mStrategyFactory
					.getPathProgramCache().getPathProgramCount(mCounterexample)) {
				final String taskDescription = "bailout by path program count limit in iteration " + mIteration;
				throw new TaskCanceledException(UserDefinedLimit.PATH_PROGRAM_ATTEMPTS, getClass(), taskDescription);
			}
			final IRefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(mCounterexample, mAbstraction,
					new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()),
					mPredicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider());
			mRefinementEngine = new TraceAbstractionRefinementEngine<>(mLogger, strategy);
		} catch (final ToolchainCanceledException tce) {
			final int traceHistogramMax = new HistogramOfIterable<>(mCounterexample.getWord()).getMax();
			final String taskDescription = "analyzing trace of length " + mCounterexample.getLength()
					+ " with TraceHistMax " + traceHistogramMax;
			tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
			throw tce;
		}

		final LBool feasibility = mRefinementEngine.getCounterexampleFeasibility();

		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample might be feasible");
			if (mRefinementEngine.providesIcfgProgramExecution()) {
				mRcfgProgramExecution = mRefinementEngine.getIcfgProgramExecution();
			} else {
				mRcfgProgramExecution =
						TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(mCounterexample.getWord());
			}

			if (mFaultLocalizationMode != RelevanceAnalysisMode.NONE && feasibility == LBool.SAT) {
				final INestedWordAutomaton<L, IPredicate> cfg = CFG2NestedWordAutomaton
						.constructAutomatonWithSPredicates(mServices, super.mIcfg, mStateFactoryForRefinement,
								super.mErrorLocs, mPref.interprocedural(), mPredicateFactory);
				final FlowSensitiveFaultLocalizer<L> fl = new FlowSensitiveFaultLocalizer<>(
						(NestedRun<L, IPredicate>) mCounterexample, cfg, mServices, mCsToolkit, mPredicateFactory,
						mCsToolkit.getModifiableGlobalsTable(), mRefinementEngine.getPredicateUnifier(),
						mFaultLocalizationMode, mSimplificationTechnique, mXnfConversionTechnique,
						mIcfg.getCfgSmtToolkit().getSymbolTable(), (IIcfg<IcfgLocation>) mIcfg);
				if (mRcfgProgramExecution instanceof IcfgProgramExecution) {
					mRcfgProgramExecution = ((IcfgProgramExecution<L>) mRcfgProgramExecution)
							.addRelevanceInformation(fl.getRelevanceInformation());
				} else {
					throw new UnsupportedOperationException("Program execution is not " + IcfgProgramExecution.class);
				}

				if (mFaultLocalizationAngelic) {
					mRcfgProgramExecution =
							new IcfgAngelicProgramExecution<>(mRcfgProgramExecution, fl.getAngelicStatus());
				}
			}
		} else {
			if (DUMP_DIFFICULT_PATH_PROGRAMS) {
				mPathProgramDumpController.reportPathProgram((NestedRun<L, IPredicate>) mCounterexample,
						((TraceAbstractionRefinementEngine<L>) mRefinementEngine).somePerfectSequenceFound(),
						mIteration);
			}
		}

		mCegarLoopBenchmark.addRefinementEngineStatistics(mRefinementEngine.getRefinementEngineStatistics());
		return feasibility;
	}

	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		mInterpolAutomaton = mRefinementEngine.getInfeasibilityProof();

		if (mPref.dumpAutomata()) {
			final String filename =
					new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()) + "_RawFloydHoareAutomaton";
			super.writeAutomatonToFile(mInterpolAutomaton, filename);
		}

		assert isInterpolantAutomatonOfSingleStateType(mInterpolAutomaton);
		if (NON_EA_INDUCTIVITY_CHECK) {
			final boolean inductive = new InductivityCheck<>(mServices, mInterpolAutomaton, false, true,
					new IncrementalHoareTripleChecker(super.mCsToolkit, false)).getResult();

			if (!inductive) {
				throw new AssertionError("not inductive");
			}
		}

		assert accepts(mServices, mInterpolAutomaton, mCounterexample.getWord(),
				false) : "Interpolant automaton broken!: " + mCounterexample.getWord() + " not accepted";

		// FIXME (Dominik 2020-12-19): The assertion below is problematic, because it has side-effects!
		// In particular, InductivityCheck calls IncrementalHoareTripleChecker, which in the method unAssertCodeBlock
		// unlocks a ManagedScript. If assertions are disabled, this remains locked. This leads to exceptions if other
		// callers try to lock it. With assertions enabled, the line below causes the ManagedScript to be unlocked and
		// no exceptions occur.
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
				mRefinementEngine.getPredicateUnifier(), mCsToolkit, mSimplificationTechnique, mXnfConversionTechnique,
				mIcfg.getCfgSmtToolkit().getSymbolTable(), mPredicateFactoryInterpolantAutomata,
				(INestedWordAutomaton<L, IPredicate>) mAbstraction, mIteration);

		mInterpolAutomaton = null;
		final NestedWordAutomaton<L, IPredicate> resultBeforeEnhancement =
				mErrorGeneralizationEngine.getResultBeforeEnhancement();
		assert isInterpolantAutomatonOfSingleStateType(resultBeforeEnhancement);
		assert accepts(mServices, resultBeforeEnhancement, mCounterexample.getWord(),
				false) : "Error automaton broken!";
	}

	@Override
	protected void reportErrorAutomatonBenchmarks() {
		mErrorGeneralizationEngine.reportErrorGeneralizationBenchmarks();
	}

	protected final IHoareTripleChecker getHoareTripleChecker() {
		final IHoareTripleChecker refinementHtc = mRefinementEngine.getHoareTripleChecker();
		if (refinementHtc != null) {
			return refinementHtc;
		}

		return TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
				mPref.getHoareTripleChecks(), mCsToolkit, mRefinementEngine.getPredicateUnifier());
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(mIteration);
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());

		final INestedWordAutomaton<L, IPredicate> minuend = (INestedWordAutomaton<L, IPredicate>) mAbstraction;

		final IPredicateUnifier predicateUnifier = mRefinementEngine.getPredicateUnifier();
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
			exploitSigmaStarConcatOfIa = !mComputeHoareAnnotation;
			subtrahendBeforeEnhancement = mInterpolAutomaton;
			enhanceMode = mPref.interpolantAutomatonEnhancement();
			subtrahend = enhanceInterpolantAutomaton(enhanceMode, predicateUnifier, htc, subtrahendBeforeEnhancement);
		}

		// TODO: HTC and predicateunifier statistics are saved in the following method, but it seems better to save them
		// at the end of the htc lifecycle instead of there
		computeAutomataDifference(minuend, subtrahend, subtrahendBeforeEnhancement, predicateUnifier,
				exploitSigmaStarConcatOfIa, htc, enhanceMode, useErrorAutomaton, automatonType);

		mLogger.info(predicateUnifier.collectPredicateUnifierStatistics());

		minimizeAbstractionIfEnabled();

		final boolean stillAccepted = new Accepts<>(new AutomataLibraryServices(mServices),
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction,
				(NestedWord<L>) mCounterexample.getWord()).getResult();
		return !stillAccepted;
	}

	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> enhanceInterpolantAutomaton(
			final InterpolantAutomatonEnhancement enhanceMode, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc, final NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		if (enhanceMode == InterpolantAutomatonEnhancement.NONE) {
			subtrahend = interpolantAutomaton;
		} else {
			final AbstractInterpolantAutomaton<L> ia = constructInterpolantAutomatonForOnDemandEnhancement(
					interpolantAutomaton, predicateUnifier, htc, enhanceMode);
			subtrahend = ia;
			if (mStoreFloydHoareAutomata) {
				mFloydHoareAutomata.add(new Pair<>(ia, predicateUnifier));
			}
		}
		return subtrahend;
	}

	/**
	 *
	 * @return true iff all traces of the path program defined by the counterexample of this iteration were subtracted
	 *         from the abstraction
	 */
	private boolean checkPathProgramRemoval()
			throws AutomataLibraryException, AutomataOperationCanceledException, AssertionError {
		final boolean pathProgramShouldHaveBeenRemoved = mRefinementEngine.somePerfectSequenceFound()
				&& mPref.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NONE;
		if (!pathProgramShouldHaveBeenRemoved) {
			return true;
		}
		final Set<L> counterexampleLetters = mCounterexample.getWord().asSet();
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
		final VpAlphabet<L> newVpAlphabet = CFG2NestedWordAutomaton.extractVpAlphabet(mIcfg, !mPref.interprocedural());
		final VpAlphabet<L> oldVpAlphabet = new VpAlphabet<>(newVpAlphabet, (Map<L, L>) newTransition2OldTransition);
		final INestedWordAutomaton<L, IPredicate> pathProgramAutomaton =
				CFG2NestedWordAutomaton.constructAutomatonWithDebugPredicates(mServices, pp,
						mPredicateFactoryResultChecking, Collections.singleton(oldLocation2NewLocation.get(errorLoc)),
						mPref.interprocedural(), newVpAlphabet, newTransition2OldTransition);
		assert pathProgramAutomaton.getFinalStates().size() == 1 : "incorrect accepting states";
		final INestedWordAutomaton<L, IPredicate> intersection =
				new Intersect<>(new AutomataLibraryServices(mServices), mPredicateFactoryResultChecking,
						(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction, pathProgramAutomaton)
								.getResult();
		final Boolean isEmpty = new IsEmpty<>(new AutomataLibraryServices(mServices), intersection).getResult();
		return isEmpty;
	}

	private void computeAutomataDifference(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final IPredicateUnifier predicateUnifier, final boolean explointSigmaStarConcatOfIA,
			final IHoareTripleChecker htc, final InterpolantAutomatonEnhancement enhanceMode,
			final boolean useErrorAutomaton, final AutomatonType automatonType)
			throws AutomataLibraryException, AutomataOperationCanceledException, AssertionError {
		try {
			mLogger.debug("Start constructing difference");
			final PowersetDeterminizer<L, IPredicate> psd =
					new PowersetDeterminizer<>(subtrahend, true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
			try {
				if (mPref.differenceSenwa()) {
					diff = new DifferenceSenwa<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
							minuend, subtrahend, psd, false);
				} else {
					diff = new Difference<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement, minuend,
							subtrahend, psd, explointSigmaStarConcatOfIA);
				}
				mCegarLoopBenchmark.reportInterpolantAutomatonStates(subtrahend.size());
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
					((AbstractInterpolantAutomaton<L>) subtrahend).switchToReadonlyMode();
				}
			}

			if (mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration)) {
				mErrorGeneralizationEngine.stopDifference(minuend, mPredicateFactoryInterpolantAutomata,
						mPredicateFactoryResultChecking, mCounterexample, false);
				final INestedWordAutomaton<L, IPredicate> cfg = CFG2NestedWordAutomaton
						.constructAutomatonWithSPredicates(mServices, super.mIcfg, mStateFactoryForRefinement,
								super.mErrorLocs, mPref.interprocedural(), mPredicateFactory);
				mErrorGeneralizationEngine.faultLocalizationWithStorage(cfg, mCsToolkit, mPredicateFactory,
						mRefinementEngine.getPredicateUnifier(), mSimplificationTechnique, mXnfConversionTechnique,
						mIcfg.getCfgSmtToolkit().getSymbolTable(), null, (NestedRun<L, IPredicate>) mCounterexample,
						(IIcfg<IcfgLocation>) mIcfg);
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
				if (mComputeHoareAnnotation) {
					final Difference<L, IPredicate> difference = (Difference<L, IPredicate>) diff;
					mHaf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
				}
				diff.removeDeadEnds();
				if (mComputeHoareAnnotation) {
					mHaf.addDeadEndDoubleDeckers(diff);
				}
			}
			mAbstraction = diff.getResult();
			if (mPref.dumpAutomata()) {
				final String filename = new SubtaskIterationIdentifier(mTaskIdentifier, getIteration())
						+ "AbstractionAfterDifferenceAndDeadEndRemoval";
				super.writeAutomatonToFile(mAbstraction, filename);
			}

		} finally {
			mCegarLoopBenchmark.addEdgeCheckerData(htc.getEdgeCheckerBenchmark());
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

	protected void dumpOrAppendAutomatonForReuseIfEnabled(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton,
			final IPredicateUnifier predicateUnifier) {
		if (mPref.dumpOnlyReuseAutomata()) {

			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.DumpTime);
			mLogger.info("Dumping reuse automata for " + mTaskIdentifier.toString() + " " + automaton.getClass());
			final String filename = mTaskIdentifier + "-reuse";
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> printedAutomaton;
			final AutomataLibraryServices services = new AutomataLibraryServices(mServices);
			final boolean addPredicateImplicationInformation = true;
			if (addPredicateImplicationInformation) {
				final HashRelation<IPredicate, IPredicate> outgoingEpsilonTransitions =
						predicateUnifier.getCoverageRelation().getCopyOfImplicationRelation();
				INestedWordAutomaton<L, IPredicate> backingNestedWordAutomaton;
				try {
					backingNestedWordAutomaton = new RemoveDeadEnds<>(services, automaton).getResult();
					if (backingNestedWordAutomaton.getStates().isEmpty()) {
						mLogger.warn("Automaton with emtpy language -- ommited dump");
						mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DumpTime);
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
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DumpTime);
		}
	}

	private void checkEnhancement(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> inputInterpolantAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException, AssertionError, AutomataOperationCanceledException {
		if (!new Accepts<>(new AutomataLibraryServices(mServices), interpolantAutomaton,
				(NestedWord<L>) mCounterexample.getWord(), true, false).getResult()) {

			final boolean isOriginalBroken = !new Accepts<>(new AutomataLibraryServices(mServices),
					inputInterpolantAutomaton, (NestedWord<L>) mCounterexample.getWord(), true, false).getResult();
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
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> enhancedInterpolantAutomaton,
			final IRun<L, ?> counterexample) {
		mLogger.fatal("--");
		mLogger.fatal("enhanced interpolant automaton broken: counterexample not accepted");
		mLogger.fatal("word:");
		for (final L letter : counterexample.getWord()) {
			mLogger.fatal(letter);
		}
		mLogger.fatal("original automaton:");
		mLogger.fatal(interpolantAutomaton);
		mLogger.fatal("enhanced automaton:");
		mLogger.fatal(enhancedInterpolantAutomaton);
		mLogger.fatal("--");
	}

	protected AbstractInterpolantAutomaton<L> constructInterpolantAutomatonForOnDemandEnhancement(
			final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		final AbstractInterpolantAutomaton<L> result;
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

	private NondeterministicInterpolantAutomaton<L> constructInterpolantAutomatonForOnDemandEnhancementEager(
			final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		final boolean conservativeSuccessorCandidateSelection =
				enhanceMode == InterpolantAutomatonEnhancement.EAGER_CONSERVATIVE;
		final boolean secondChance = enhanceMode != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE;
		return new NondeterministicInterpolantAutomaton<>(mServices, mCsToolkit, htc, inputInterpolantAutomaton,
				predicateUnifier, conservativeSuccessorCandidateSelection, secondChance);
	}

	private DeterministicInterpolantAutomaton<L>
			constructInterpolantAutomatonForOnDemandEnhancementPredicateAbstraction(
					final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
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
	protected void minimizeAbstraction(final PredicateFactoryRefinement predicateFactoryRefinement,
			final PredicateFactoryResultChecking resultCheckPredFac, final Minimization minimization)
			throws AutomataOperationCanceledException, AutomataLibraryException, AssertionError {

		final Function<IPredicate, Set<IcfgLocation>> lcsProvider =
				x -> (x instanceof ISLPredicate ? Collections.singleton(((ISLPredicate) x).getProgramPoint())
						: new HashSet<>(Arrays.asList(((IMLPredicate) x).getProgramPoints())));
		AutomataMinimization<Set<IcfgLocation>, IPredicate, L> am;
		try {
			am = new AutomataMinimization<>(mServices, (INestedWordAutomaton<L, IPredicate>) mAbstraction, minimization,
					mComputeHoareAnnotation, mIteration, predicateFactoryRefinement, MINIMIZE_EVERY_KTH_ITERATION,
					mStoredRawInterpolantAutomata, mInterpolAutomaton, MINIMIZATION_TIMEOUT, resultCheckPredFac,
					lcsProvider, true);
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
		final INestedWordAutomaton<L, IPredicate> abstraction = (INestedWordAutomaton<L, IPredicate>) mAbstraction;
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
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> nia, final Word<L> word,
			final boolean checkAlsoForAcceptanceOfSomePrefix) throws AutomataOperationCanceledException {
		try {
			return new Accepts<>(new AutomataLibraryServices(services), nia, NestedWord.nestedWord(word),
					checkAlsoForAcceptanceOfSomePrefix, false).getResult();
		} catch (final AutomataOperationCanceledException e) {
			throw e;
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}

	public IStatisticsDataProvider getCegarLoopBenchmark() {
		return mCegarLoopBenchmark;
	}

	/**
	 * method called at the end of the cegar loop
	 */
	public void finish() {
		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());
	}

	@Override
	protected boolean isResultUnsafe(final boolean errorGeneralizationEnabled, final Result abstractResult) {
		if (!errorGeneralizationEnabled) {
			return false;
		}
		final INestedWordAutomaton<L, IPredicate> cfg =
				CFG2NestedWordAutomaton.constructAutomatonWithSPredicates(mServices, super.mIcfg,
						mStateFactoryForRefinement, super.mErrorLocs, mPref.interprocedural(), mPredicateFactory);
		return mErrorGeneralizationEngine.isResultUnsafe(abstractResult, cfg, mCsToolkit, mPredicateFactory,
				mRefinementEngine.getPredicateUnifier(), mSimplificationTechnique, mXnfConversionTechnique,
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

	public LinkedHashSet<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> getFloydHoareAutomata() {
		if (mStoreFloydHoareAutomata) {
			return mFloydHoareAutomata;
		}
		throw new IllegalStateException("Floyd-Hoare automata have not been stored");
	}

	public IPreconditionProvider getPreconditionProvider() {
		return IPreconditionProvider.constructDefaultPreconditionProvider();
	}

	public IPostconditionProvider getPostconditionProvider() {
		return IPostconditionProvider.constructDefaultPostconditionProvider();
	}

	private final boolean isSequential() {
		return super.mIcfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().isEmpty();
	}
}
