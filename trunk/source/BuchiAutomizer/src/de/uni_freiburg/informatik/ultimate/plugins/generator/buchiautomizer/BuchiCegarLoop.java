/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiClosureNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.GeneralizedBuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsSemiDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.BenchmarkRecord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.GeneralizedBuchiToBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.GeneralizedDifference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.NumberOfTransitions;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.UtilFixedCounterexample;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskFileIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.ContinueDirective;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoCheck.TraceCheckResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.BuchiComplementationConstruction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.NcsbImplementation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryResultChecking;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimization.AutomataMinimizationTimeout;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.InterpolantAutomatonBuilderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.InterpolationPreferenceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.RefinementStrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessUtils.Property;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class BuchiCegarLoop<LETTER extends IIcfgTransition<?>> {

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

	private static final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private static final XnfConversionTechnique mXnfConversionTechnique =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private static final boolean DUMP_BIGGEST_AUTOMATON = false;

	protected static final Format PRINT_AUTOMATA_LABELING = Format.ATS;

	/**
	 * If set to false we crash if the call alphabet is not empty.
	 */
	private static final boolean ALLOW_CALLS = true;

	protected final ILogger mLogger;

	/**
	 * true iff we are run in an LTL toolchain and should report appropriate results
	 */
	private boolean mLTLMode;

	private final String mName;

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
	protected int mIteration = 0;

	/**
	 * Accepting run of the abstraction obtained in this iteration.
	 */
	protected NestedLassoRun<LETTER, IPredicate> mCounterexample;

	/**
	 * Abstraction of this iteration. The language of mAbstraction is a set of traces which is
	 * <ul>
	 * <li>a superset of the feasible program traces.
	 * <li>a subset of the traces which respect the control flow of of the program.
	 */
	protected INestedWordAutomaton<LETTER, IPredicate> mAbstraction;

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected NestedWordAutomaton<LETTER, IPredicate> mInterpolAutomaton;

	protected IAutomaton<LETTER, IPredicate> mArtifactAutomaton;

	// used for the collection of statistics
	int mInfeasible = 0;
	int mRankWithoutSi = 0;
	int mRankWithSi = 0;

	private final PredicateFactoryForInterpolantAutomata mDefaultStateFactory;
	private final PredicateFactoryResultChecking mPredicateFactoryResultChecking;

	private final PredicateFactoryRefinement mStateFactoryForRefinement;

	private final BuchiAutomizerModuleDecompositionBenchmark mMDBenchmark;

	private final BuchiCegarLoopBenchmarkGenerator mBenchmarkGenerator;

	private final boolean mDifference;
	private final boolean mUseDoubleDeckers;
	private final BuchiComplementationConstruction mComplementationConstruction;

	/**
	 * Construct a termination proof in the form that is required for the Termination Competition.
	 * http://termination-portal.org/wiki/Termination_Competition This proof is finally print in the console output and
	 * can be huge.
	 */
	private final boolean mConstructTermcompProof;
	private final TermcompProofBenchmark mTermcompProofBenchmark;

	private final InterpolationTechnique mInterpolation;

	private final RefineBuchi<LETTER> mRefineBuchi;
	private final List<BuchiInterpolantAutomatonConstructionStyle> mBiaConstructionStyleSequence;

	private final Minimization mAutomataMinimizationAfterFeasbilityBasedRefinement;
	private final Minimization mAutomataMinimizationAfterRankBasedRefinement;

	private NonTerminationArgument mNonterminationArgument;

	private final IUltimateServiceProvider mServices;

	private ToolchainCanceledException mToolchainCancelledException;
	private final RankVarConstructor mRankVarConstructor;

	private final RefinementStrategyFactory<LETTER> mRefinementStrategyFactory;
	private final TaskIdentifier mTaskIdentifier;

	private final INestedWordAutomaton<WitnessEdge, WitnessNode> mWitnessAutomaton;

	public ToolchainCanceledException getToolchainCancelledException() {
		return mToolchainCancelledException;
	}

	public NonTerminationArgument getNonTerminationArgument() {
		return mNonterminationArgument;
	}

	public BuchiCegarLoop(final IIcfg<?> icfg, final CfgSmtToolkit csToolkitWithoutRankVars,
			final RankVarConstructor rankVarConstructor, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final IUltimateServiceProvider services,
			final INestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		assert services != null;
		mIcfg = icfg;
		// TODO: TaskIdentifier should probably be provided by caller
		mTaskIdentifier = new SubtaskFileIdentifier(null, mIcfg.getIdentifier());
		mLTLMode = false;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mMDBenchmark = new BuchiAutomizerModuleDecompositionBenchmark(mServices.getBacktranslationService());
		mName = "BuchiCegarLoop";
		mPredicateFactory = predicateFactory;
		mWitnessAutomaton = witnessAutomaton;
		mRankVarConstructor = rankVarConstructor;
		mCsToolkitWithoutRankVars = csToolkitWithoutRankVars;
		mCsToolkitWithRankVars = mRankVarConstructor.getCsToolkitWithRankVariables();
		mBinaryStatePredicateManager = new BinaryStatePredicateManager(mCsToolkitWithRankVars, predicateFactory,
				mRankVarConstructor.getUnseededVariable(), mRankVarConstructor.getOldRankVariables(), mServices,
				mSimplificationTechnique, mXnfConversionTechnique);
		mBenchmarkGenerator = new BuchiCegarLoopBenchmarkGenerator();
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.OverallTime.toString());
		// this.buchiModGlobalVarManager = new BuchiModGlobalVarManager(
		// mBspm.getUnseededVariable(), mBspm.getOldRankVariable(),
		// mRootAnnot.getModGlobVarManager(),
		// mRootAnnot.getBoogie2SMT());

		mPref = taPrefs;
		mDefaultStateFactory = new PredicateFactoryForInterpolantAutomata(mCsToolkitWithRankVars.getManagedScript(),
				predicateFactory, mPref.computeHoareAnnotation());
		mPredicateFactoryResultChecking = new PredicateFactoryResultChecking(predicateFactory);

		mStateFactoryForRefinement = new PredicateFactoryRefinement(mServices,
				mCsToolkitWithRankVars.getManagedScript(), predicateFactory, false, Collections.emptySet());

		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		mUseDoubleDeckers = !baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_IGNORE_DOWN_STATES);
		mDifference = baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_DETERMINIZATION_ON_DEMAND);

		mComplementationConstruction =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_BUCHI_COMPLEMENTATION_CONSTRUCTION,
						BuchiComplementationConstruction.class);

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
		if (mConstructTermcompProof) {
			mTermcompProofBenchmark = new TermcompProofBenchmark(mServices);
		} else {
			mTermcompProofBenchmark = null;
		}

		final NcsbImplementation ncsbImplemntation =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_NCSB_IMPLEMENTATION, NcsbImplementation.class);
		mRefineBuchi = new RefineBuchi<>(mIcfg, mCsToolkitWithRankVars, predicateFactory, mPref.dumpAutomata(),
				mDifference, mDefaultStateFactory, mStateFactoryForRefinement, mUseDoubleDeckers, mPref.dumpPath(),
				mPref.getAutomataFormat(), mInterpolation, mServices, mLogger, mSimplificationTechnique,
				mXnfConversionTechnique, ncsbImplemntation);
		final BuchiInterpolantAutomatonConstructionStrategy biaConstructionStrategy =
				baPref.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_BIA_CONSTRUCTION_STRATEGY,
						BuchiInterpolantAutomatonConstructionStrategy.class);
		mBiaConstructionStyleSequence = biaConstructionStrategy.getBiaConstrucionStyleSequence(baPref);

		{
			final PathProgramCache<LETTER> pathProgramCache = new PathProgramCache<>(mLogger);
			final CegarAbsIntRunner<LETTER> absIntRunner =
					new CegarAbsIntRunner<>(services, mBenchmarkGenerator, mIcfg, mSimplificationTechnique,
							mXnfConversionTechnique, mCsToolkitWithoutRankVars, pathProgramCache, taPrefs);
			final InterpolantAutomatonBuilderFactory<LETTER> mInterpolantAutomatonBuilderFactory =
					new InterpolantAutomatonBuilderFactory<>(mServices, mCsToolkitWithoutRankVars, mDefaultStateFactory,
							mIcfg, absIntRunner, taPrefs, mInterpolation, mPref.interpolantAutomaton(),
							mBenchmarkGenerator);
			final TaCheckAndRefinementPreferences<LETTER> taCheckAndRefinementPrefs =
					new TaCheckAndRefinementPreferences<>(mServices, mPref, mInterpolation, mSimplificationTechnique,
							mXnfConversionTechnique, mCsToolkitWithoutRankVars, mPredicateFactory, mIcfg,
							mInterpolantAutomatonBuilderFactory);
			mRefinementStrategyFactory = new RefinementStrategyFactory<>(mLogger, mServices, mPref, taCheckAndRefinementPrefs,
					absIntRunner, mIcfg, mPredicateFactory, pathProgramCache);
		}
	}

	NestedLassoRun<LETTER, IPredicate> getCounterexample() {
		return mCounterexample;
	}

	static boolean isEmptyStem(final NestedLassoRun<?, IPredicate> nlr) {
		assert nlr.getStem().getLength() > 0;
		return nlr.getStem().getLength() == 1;
	}

	public final Result iterate() throws IOException {
		mLogger.info("Interprodecural is " + mPref.interprocedural());
		mLogger.info("Hoare is " + mPref.computeHoareAnnotation());
		mLogger.info("Compute interpolants for " + mInterpolation);
		mLogger.info("Backedges is " + mPref.interpolantAutomaton());
		mLogger.info("Determinization is " + mPref.interpolantAutomatonEnhancement());
		mLogger.info("Difference is " + mPref.differenceSenwa());
		mLogger.info("Minimize is " + mPref.getMinimization());

		mIteration = 0;
		mLogger.info("======== Iteration " + mIteration + "==of CEGAR loop == " + mName + "========");

		getInitialAbstraction();

		if (mIteration <= mPref.watchIteration()
				&& (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.RCFG)) {
			mArtifactAutomaton = mAbstraction;
		}
		if (mPref.dumpAutomata()) {
			final String filename = mIcfg.getIdentifier() + "_" + mName + "Abstraction" + mIteration;
			if (mAbstraction instanceof IGeneralizedNestedWordAutomaton) {
				final GeneralizedBuchiToBuchi<LETTER, IPredicate> gba2ba =
						new GeneralizedBuchiToBuchi<>(mStateFactoryForRefinement, mAbstraction);
				writeAutomatonToFile(mServices, gba2ba, mPref.dumpPath(), filename, mPref.getAutomataFormat(), "");
			} else {
				writeAutomatonToFile(mServices, mAbstraction, mPref.dumpPath(), filename, mPref.getAutomataFormat(),
						"");
			}
		}

		// DD: Please take care that you do not commit enabled debug code. You should ask Matthias about integrating
		// your own statistics into Ultimate's .csv infrastructure.
		// YFC: Now by default it is disabled. It is enabled only when a special file machine.conf is in the system.
		// By default no machine.conf
		final boolean pldiDump = BenchmarkRecord.canDump();
		if (pldiDump) {
			BenchmarkRecord.start(mIcfg.getIdentifier() + "_" + mName,
					mServices.getPreferenceProvider(Activator.PLUGIN_ID)
							.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_NCSB_IMPLEMENTATION,
									NcsbImplementation.class)
							.toString()
							+ "+"
							+ mServices.getPreferenceProvider(Activator.PLUGIN_ID).getEnum(
									BuchiAutomizerPreferenceInitializer.LABEL_BIA_CONSTRUCTION_STRATEGY,
									BuchiInterpolantAutomatonConstructionStrategy.class));
		}
		boolean initalAbstractionCorrect;
		try {
			initalAbstractionCorrect = isAbstractionCorrect();
		} catch (final AutomataLibraryException e1) {
			mLogger.warn("Verification cancelled");
			mMDBenchmark.reportRemainderModule(mAbstraction.size(), false);
			mBenchmarkGenerator.setResult(Result.TIMEOUT);
			mToolchainCancelledException = new ToolchainCanceledException(e1.getClassOfThrower());
			if (pldiDump) {
				BenchmarkRecord.finish();
			}
			return Result.TIMEOUT;
		}
		if (initalAbstractionCorrect) {
			mMDBenchmark.reportNoRemainderModule();
			mBenchmarkGenerator.setResult(Result.TERMINATING);
			if (pldiDump) {
				BenchmarkRecord.finish();
			}
			return Result.TERMINATING;
		}

		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			mLogger.info("======== Iteration " + mIteration + "============");
			mBenchmarkGenerator.announceNextIteration();
			boolean abstractionCorrect;
			try {
				abstractionCorrect = isAbstractionCorrect();
			} catch (final AutomataLibraryException e1) {
				mLogger.warn("Verification cancelled");
				mMDBenchmark.reportRemainderModule(mAbstraction.size(), false);
				if (mConstructTermcompProof) {
					mTermcompProofBenchmark.reportRemainderModule(false);
				}
				mBenchmarkGenerator.setResult(Result.TIMEOUT);
				mToolchainCancelledException = new ToolchainCanceledException(e1.getClassOfThrower());
				if (pldiDump) {
					BenchmarkRecord.finish();
				}
				return Result.TIMEOUT;
			}
			if (abstractionCorrect) {
				mMDBenchmark.reportNoRemainderModule();
				if (mConstructTermcompProof) {
					mTermcompProofBenchmark.reportNoRemainderModule();
				}
				mBenchmarkGenerator.setResult(Result.TERMINATING);
				if (pldiDump) {
					BenchmarkRecord.finish();
				}
				return Result.TERMINATING;
			}

			LassoCheck<LETTER> lassoCheck;
			try {
				final TaskIdentifier taskIdentifier = new SubtaskIterationIdentifier(mTaskIdentifier, mIteration);
				mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.s_LassoAnalysisTime);
				lassoCheck = new LassoCheck<>(mInterpolation, mCsToolkitWithoutRankVars, mPredicateFactory,
						mCsToolkitWithRankVars.getSymbolTable(), mCsToolkitWithoutRankVars.getModifiableGlobalsTable(),
						mIcfg.getCfgSmtToolkit().getSmtFunctionsAndAxioms(), mBinaryStatePredicateManager, mCounterexample,
						generateLassoCheckIdentifier(), mServices, mSimplificationTechnique, mXnfConversionTechnique,
						mRefinementStrategyFactory, mAbstraction, taskIdentifier, mBenchmarkGenerator);
				if (lassoCheck.getLassoCheckResult().getContinueDirective() == ContinueDirective.REPORT_UNKNOWN) {
					// if result was unknown, then try again but this time add one
					// iteration of the loop to the stem.
					// This allows us to verify Vincent's coolant examples
					final TaskIdentifier unwindingTaskIdentifier =
							new SubtaskAdditionalLoopUnwinding(taskIdentifier, 1);
					mLogger.info("Result of lasso check was UNKNOWN. I will concatenate loop to stem and try again.");
					final NestedRun<LETTER, IPredicate> newStem =
							mCounterexample.getStem().concatenate(mCounterexample.getLoop());
					mCounterexample = new NestedLassoRun<>(newStem, mCounterexample.getLoop());
					lassoCheck = new LassoCheck<>(mInterpolation, mCsToolkitWithoutRankVars, mPredicateFactory,
							mIcfg.getCfgSmtToolkit().getSymbolTable(),
							mCsToolkitWithoutRankVars.getModifiableGlobalsTable(),
							mIcfg.getCfgSmtToolkit().getSmtFunctionsAndAxioms(), mBinaryStatePredicateManager, mCounterexample,
							generateLassoCheckIdentifier(), mServices, mSimplificationTechnique, mXnfConversionTechnique,
							mRefinementStrategyFactory, mAbstraction, unwindingTaskIdentifier, mBenchmarkGenerator);
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
				mBenchmarkGenerator.setResult(Result.TIMEOUT);
				if (pldiDump) {
					BenchmarkRecord.finish();
				}
				return Result.TIMEOUT;
			} finally {
				mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.s_LassoAnalysisTime);
			}

			final ContinueDirective cd = lassoCheck.getLassoCheckResult().getContinueDirective();
			mBenchmarkGenerator.reportLassoAnalysis(lassoCheck);
			try {
				switch (cd) {
				case REFINE_BOTH: {
					final BinaryStatePredicateManager bspm = lassoCheck.getBinaryStatePredicateManager();
					if (bspm.isLoopWithoutStemTerminating()) {
						mRankWithoutSi++;
					} else {
						mRankWithSi++;
					}
					final ISLPredicate hondaISLP = (ISLPredicate) mCounterexample.getLoop().getStateAtPosition(0);
					final IcfgLocation hondaPP = hondaISLP.getProgramPoint();
					final TerminationArgumentResult<IIcfgElement, Term> tar =
							constructTAResult(bspm.getTerminationArgument(), hondaPP,
									mCounterexample.getStem().getWord(), mCounterexample.getLoop().getWord());
					mMDBenchmark.reportRankingFunction(mIteration, tar);

					final INestedWordAutomaton<LETTER, IPredicate> newAbstraction = refineBuchi(lassoCheck);
					mAbstraction = newAbstraction;
					mBinaryStatePredicateManager.clearPredicates();

					reduceAbstractionSize(mAutomataMinimizationAfterRankBasedRefinement);

					refineFinite(lassoCheck);
					mInfeasible++;
					reduceAbstractionSize(mAutomataMinimizationAfterFeasbilityBasedRefinement);
				}
					break;
				case REFINE_FINITE:
					refineFinite(lassoCheck);
					mInfeasible++;
					reduceAbstractionSize(mAutomataMinimizationAfterFeasbilityBasedRefinement);
					break;

				case REFINE_BUCHI:
					final BinaryStatePredicateManager bspm = lassoCheck.getBinaryStatePredicateManager();
					if (bspm.isLoopWithoutStemTerminating()) {
						mRankWithoutSi++;
					} else {
						mRankWithSi++;
					}
					final ISLPredicate hondaISLP = (ISLPredicate) mCounterexample.getLoop().getStateAtPosition(0);
					final IcfgLocation hondaPP = hondaISLP.getProgramPoint();
					final TerminationArgumentResult<IIcfgElement, Term> tar =
							constructTAResult(bspm.getTerminationArgument(), hondaPP,
									mCounterexample.getStem().getWord(), mCounterexample.getLoop().getWord());
					mMDBenchmark.reportRankingFunction(mIteration, tar);

					final INestedWordAutomaton<LETTER, IPredicate> newAbstraction = refineBuchi(lassoCheck);
					mAbstraction = newAbstraction;
					mBinaryStatePredicateManager.clearPredicates();
					reduceAbstractionSize(mAutomataMinimizationAfterRankBasedRefinement);
					break;
				case REPORT_UNKNOWN:
					mMDBenchmark.reportRemainderModule(mAbstraction.size(), false);
					if (mConstructTermcompProof) {
						mTermcompProofBenchmark.reportRemainderModule(false);
					}
					mBenchmarkGenerator.setResult(Result.UNKNOWN);
					if (pldiDump) {
						BenchmarkRecord.finish();
					}
					return Result.UNKNOWN;
				case REPORT_NONTERMINATION:
					if (!lassoWasOverapproximated().isEmpty()) {
						mMDBenchmark.reportRemainderModule(mAbstraction.size(), false);
						if (mConstructTermcompProof) {
							mTermcompProofBenchmark.reportRemainderModule(false);
						}
						mBenchmarkGenerator.setResult(Result.UNKNOWN);
						if (pldiDump) {
							BenchmarkRecord.finish();
						}
						return Result.UNKNOWN;
					}
					mNonterminationArgument = lassoCheck.getNonTerminationArgument();
					mMDBenchmark.reportRemainderModule(mAbstraction.size(), true);
					if (mConstructTermcompProof) {
						mTermcompProofBenchmark.reportRemainderModule(true);
					}
					mBenchmarkGenerator.setResult(Result.NONTERMINATING);
					if (pldiDump) {
						BenchmarkRecord.finish();
					}
					return Result.NONTERMINATING;
				default:
					throw new AssertionError("impossible case");
				}
				mLogger.info("Abstraction has " + mAbstraction.sizeInformation());
				// s_Logger.info("Interpolant automaton has " +
				// mRefineBuchi.getInterpolAutomatonUsedInRefinement().sizeInformation());
				if (mIteration <= mPref.watchIteration() && mPref.artifact() == Artifact.ABSTRACTION) {
					mArtifactAutomaton = mAbstraction;
				}

				if (mPref.dumpAutomata()) {
					final String filename = mIcfg.getIdentifier() + "_" + mName + "Abstraction" + mIteration;
					if (mAbstraction instanceof IGeneralizedNestedWordAutomaton) {
						final GeneralizedBuchiToBuchi<LETTER, IPredicate> gba2ba =
								new GeneralizedBuchiToBuchi<>(mStateFactoryForRefinement, mAbstraction);
						writeAutomatonToFile(mServices, gba2ba, mPref.dumpPath(), filename, mPref.getAutomataFormat(),
								"");
					} else {
						writeAutomatonToFile(mServices, mAbstraction, mPref.dumpPath(), filename,
								mPref.getAutomataFormat(), "");
					}
				}
				final boolean newMaximumReached =
						mBenchmarkGenerator.reportAbstractionSize(mAbstraction.size(), mIteration);
				if (DUMP_BIGGEST_AUTOMATON && mIteration > 4 && newMaximumReached) {
					final String filename = mIcfg.getIdentifier();
					writeAutomatonToFile(mServices, mAbstraction, mPref.dumpPath(), filename, mPref.getAutomataFormat(),
							"");
				}

			} catch (final AutomataOperationCanceledException e) {
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(), "performing iteration " + mIteration);
				mToolchainCancelledException = new ToolchainCanceledException(e, rti);
				mBenchmarkGenerator.setResult(Result.TIMEOUT);
				if (pldiDump) {
					BenchmarkRecord.finish();
				}
				return Result.TIMEOUT;
			} catch (final ToolchainCanceledException e) {
				mToolchainCancelledException = e;
				mBenchmarkGenerator.setResult(Result.TIMEOUT);
				if (pldiDump) {
					BenchmarkRecord.finish();
				}
				return Result.TIMEOUT;
			}
			mInterpolAutomaton = null;
		}
		mBenchmarkGenerator.setResult(Result.TIMEOUT);
		return Result.TIMEOUT;
	}

	private Map<String, ILocation> lassoWasOverapproximated() {
		final NestedWord<LETTER> stem = mCounterexample.getStem().getWord();
		final NestedWord<LETTER> loop = mCounterexample.getLoop().getWord();
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
	private void reduceAbstractionSize(final Minimization automataMinimization)
			throws AutomataOperationCanceledException, AssertionError {
		// added by Yu-Fang Chen for experiments, if machine.conf is there, disable minimization
		if (BenchmarkRecord.canDump()) {
			return;
		}
		// end of the code added by Yu-Fang Chen

		if ((mAbstraction instanceof IGeneralizedNestedWordAutomaton)) {
			return;// GBA does not have minimization support yet.
		}

		mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.s_NonLiveStateRemoval);
		try {
			mAbstraction = new RemoveNonLiveStates<>(new AutomataLibraryServices(mServices), mAbstraction).getResult();
		} finally {
			mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.s_NonLiveStateRemoval);
		}
		mBenchmarkGenerator.start(BuchiCegarLoopBenchmark.s_BuchiClosure);
		try {
			mAbstraction = new BuchiClosureNwa<>(new AutomataLibraryServices(mServices), mAbstraction);
			// mAbstraction = (new RemoveDeadEnds<LETTER, IPredicate>(mServices, mAbstraction)).getResult();
		} finally {
			mBenchmarkGenerator.stop(BuchiCegarLoopBenchmark.s_BuchiClosure);
		}
		try {
			final boolean isDeterministic =
					new IsDeterministic<>(new AutomataLibraryServices(mServices), mAbstraction).getResult();
			if (isDeterministic) {
				mBenchmarkGenerator.reportMinimizationOfDetAutom();
			} else {
				mBenchmarkGenerator.reportMinimizationOfNondetAutom();
			}
			mLogger.info("Abstraction has " + mAbstraction.sizeInformation());

			if (mAbstraction.size() > 0) {
				final Function<ISLPredicate, IcfgLocation> locProvider = x -> x.getProgramPoint();
				AutomataMinimization<IcfgLocation, ISLPredicate, LETTER> am;
				try {
					am = new AutomataMinimization<>(mServices, mAbstraction, automataMinimization, false, mIteration,
							mStateFactoryForRefinement, -1, null, mInterpolAutomaton, -1,
							mPredicateFactoryResultChecking, locProvider, false);
				} catch (final AutomataMinimizationTimeout e) {
					mBenchmarkGenerator.addAutomataMinimizationData(e.getStatistics());
					throw e.getAutomataOperationCanceledException();
				}
				mBenchmarkGenerator.addAutomataMinimizationData(am.getStatistics());
				if (am.newAutomatonWasBuilt()) {
					mAbstraction = am.getMinimizedAutomaton();
				}
			}
		} catch (final AutomataOperationCanceledException e) {
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
					"minimizing (" + automataMinimization + ") automaton with " + mAbstraction.size() + " states");
			throw new ToolchainCanceledException(e, rti);
		}
		mLogger.info("Abstraction has " + mAbstraction.sizeInformation());
	}

	private INestedWordAutomaton<LETTER, IPredicate> refineBuchi(final LassoCheck<LETTER> lassoCheck)
			throws AutomataOperationCanceledException {
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		int stage = 0;
		// final BuchiModGlobalVarManager bmgvm = new BuchiModGlobalVarManager(
		// lassoChecker.getBinaryStatePredicateManager().getUnseededVariable(),
		// lassoChecker.getBinaryStatePredicateManager().getOldRankVariables(),
		// mRootAnnot.getCfgSmtToolkit().getModifiableGlobals(), mRootAnnot.getBoogie2SMT());

		/*
		 * Iterate through a sequence of BuchiInterpolantAutomatonConstructionStyles Each construction style defines how
		 * an interpolant automaton is constructed. Constructions that provide simpler (less nondeterministic) automata
		 * should come first. In each iteration we compute the difference which causes an on-demand construciton of the
		 * automaton and evaluate the automaton afterwards. If the automaton is "good" we keep the difference and
		 * continued with the termination analysis. If the automaton is "bad" we construct the next automaton. Currently
		 * an automaton is "good" iff the counterexample of the current CEGAR iteration is accepted by the automaton
		 * (otherwise the counterexample would not be excluded and we might get it again in the next iteration of the
		 * CEGAR loop).
		 *
		 */
		for (final BuchiInterpolantAutomatonConstructionStyle constructionStyle : mBiaConstructionStyleSequence) {
			assert automatonUsesISLPredicates(mAbstraction) : "used wrong StateFactory";
			INestedWordAutomaton<LETTER, IPredicate> newAbstraction = null;
			try {
				newAbstraction = mRefineBuchi.refineBuchi(mAbstraction, mCounterexample, mIteration, constructionStyle,
						lassoCheck.getBinaryStatePredicateManager(), mCsToolkitWithRankVars.getModifiableGlobalsTable(),
						mInterpolation, mBenchmarkGenerator, mComplementationConstruction);
			} catch (final AutomataOperationCanceledException e) {
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(), "applying stage " + stage);
				throw new ToolchainCanceledException(e, rti);
			} catch (final ToolchainCanceledException e) {
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				throw e;
			} catch (final AutomataLibraryException e) {
				throw new AssertionError(e.getMessage());
			}

			if (BenchmarkRecord.canDump()) {
				dumpAutomatonInformation(mRefineBuchi.getInterpolAutomatonUsedInRefinement(), false);
			}
			// UtilFixedCounterexample<LETTER, IPredicate> utilFixedCe = new UtilFixedCounterexample<>();
			// final String counterName = mIcfg.getIdentifier() + "_" + mName + "Abstraction";
			// try {
			// System.err.println("At iteration number " + mIteration);
			// utilFixedCe.checkAcceptance(new AutomataLibraryServices(mServices),
			// mRefineBuchi.getInterpolAutomatonUsedInRefinement(), counterName, 5);
			// utilFixedCe.checkAcceptance(new AutomataLibraryServices(mServices), mAbstraction, counterName, 5);
			// } catch (AutomataLibraryException e1) {
			// // TODO Auto-generated catch block
			// e1.printStackTrace();
			// }
			if (newAbstraction != null) {
				if (mConstructTermcompProof) {
					mTermcompProofBenchmark.reportBuchiModule(mIteration,
							mRefineBuchi.getInterpolAutomatonUsedInRefinement());
				}
				mBenchmarkGenerator.announceSuccessfullRefinementStage(stage);
				switch (constructionStyle.getInterpolantAutomaton()) {
				case Deterministic:
				case LassoAutomaton:
					mMDBenchmark.reportDeterminsticModule(mIteration,
							mRefineBuchi.getInterpolAutomatonUsedInRefinement().size());
					break;
				case ScroogeNondeterminism:
				case EagerNondeterminism:
					mMDBenchmark.reportNonDeterminsticModule(mIteration,
							mRefineBuchi.getInterpolAutomatonUsedInRefinement().size());
					break;
				default:
					throw new AssertionError("unsupported");
				}
				mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
				mBenchmarkGenerator.addBackwardCoveringInformationBuchi(mRefineBuchi.getBci());
				return newAbstraction;
			}
			stage++;
		}
		throw new AssertionError("no settings was sufficient");
	}

	private boolean isAbstractionCorrect() throws AutomataLibraryException {
		// if(mAbstraction instanceof IGeneralizedNestedWordAutomaton) {
		// IGeneralizedNestedWordAutomaton<LETTER, IPredicate> abstraction
		// = (IGeneralizedNestedWordAutomaton<LETTER, IPredicate>)mAbstraction;
		// final GeneralizedBuchiIsEmpty<LETTER, IPredicate> ec =
		// new GeneralizedBuchiIsEmpty<>(new AutomataLibraryServices(mServices), abstraction);
		// if (ec.getResult()) {
		// return true;
		// }
		// mCounterexample = ec.getAcceptingNestedLassoRun();
		// }else {
		// final BuchiIsEmpty<LETTER, IPredicate> ec =
		// new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), mAbstraction);
		// if (ec.getResult()) {
		// return true;
		// }
		// mCounterexample = ec.getAcceptingNestedLassoRun();
		// }

		final String counterName = mIcfg.getIdentifier() + "_" + mName + "Abstraction";
		final UtilFixedCounterexample<LETTER, IPredicate> utilFixedCe = new UtilFixedCounterexample<>();
		final NestedLassoRun<LETTER, IPredicate> counterexample = utilFixedCe
				.getNestedLassoRun(new AutomataLibraryServices(mServices), mAbstraction, counterName, mIteration);
		if (counterexample != null) {
			mCounterexample = counterexample;
		} else {
			if (mAbstraction instanceof IGeneralizedNestedWordAutomaton) {
				final IGeneralizedNestedWordAutomaton<LETTER, IPredicate> abstraction =
						(IGeneralizedNestedWordAutomaton<LETTER, IPredicate>) mAbstraction;
				final GeneralizedBuchiIsEmpty<LETTER, IPredicate> ec =
						new GeneralizedBuchiIsEmpty<>(new AutomataLibraryServices(mServices), abstraction);
				if (ec.getResult()) {
					return true;
				}
				mCounterexample = ec.getAcceptingNestedLassoRun();
			} else {
				final BuchiIsEmpty<LETTER, IPredicate> ec =
						new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), mAbstraction);
				if (ec.getResult()) {
					return true;
				}
				mCounterexample = ec.getAcceptingNestedLassoRun();
			}
			utilFixedCe.writeNestedLassoRun(mAbstraction, mCounterexample, counterName, mIteration);
		}

		final HistogramOfIterable<LETTER> traceHistogramStem =
				new HistogramOfIterable<>(mCounterexample.getStem().getWord());
		mBenchmarkGenerator.reportTraceHistogramMaximum(traceHistogramStem.getMax());
		final HistogramOfIterable<LETTER> traceHistogramLoop =
				new HistogramOfIterable<>(mCounterexample.getLoop().getWord());
		mBenchmarkGenerator.reportTraceHistogramMaximum(traceHistogramLoop.getMax());

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Counterexample stem histogram " + traceHistogramStem);
			mLogger.info("Counterexample loop histogram " + traceHistogramLoop);
		}
		assert mCounterexample.getLoop().getLength() > 1;

		return false;
	}

	private void getInitialAbstraction() {
		final Collection<IcfgLocation> acceptingNodes;
		final Collection<IcfgLocation> allNodes = new HashSet<>();
		for (final Map<DebugIdentifier, ? extends IcfgLocation> prog2pp : mIcfg.getProgramPoints().values()) {
			allNodes.addAll(prog2pp.values());
		}

		// check if we run in LTL mode and set accepting states accordingly
		if (LTLPropertyCheck.getAnnotation(mIcfg) != null) {
			mLTLMode = true;
			acceptingNodes =
					allNodes.stream().filter(a -> BuchiProgramAcceptingStateAnnotation.getAnnotation(a) != null)
							.collect(Collectors.toSet());
		} else {
			mLTLMode = false;
			acceptingNodes = allNodes;
		}
		mAbstraction = CFG2NestedWordAutomaton.constructAutomatonWithSPredicates(mServices, mIcfg, mDefaultStateFactory,
				acceptingNodes, mPref.interprocedural(), mPredicateFactory);
		if (!ALLOW_CALLS && !mAbstraction.getVpAlphabet().getCallAlphabet().isEmpty()) {
			throw new AssertionError("Calls are not allowed in this debugging mode");
		}
		if (mWitnessAutomaton != null) {
			try {
				final AutomataLibraryServices services = new AutomataLibraryServices(mServices);
				final NestedWordAutomatonReachableStates<WitnessEdge, WitnessNode> reach =
						new NestedWordAutomatonReachableStates<>(services, mWitnessAutomaton);
				final INestedWordAutomaton<WitnessEdge, WitnessNode> allAccepting =
						new NestedWordAutomatonFilteredStates<>(services, reach, mWitnessAutomaton.getStates(),
								mWitnessAutomaton.getInitialStates(), mWitnessAutomaton.getStates());
				mAbstraction = WitnessUtils.constructIcfgAndWitnessProduct(mServices, mAbstraction, allAccepting,
						mCsToolkitWithoutRankVars, mPredicateFactory, mStateFactoryForRefinement, mLogger,
						Property.TERMINATION);
			} catch (final AutomataOperationCanceledException e) {
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
						"constructing product with witness of size " + mWitnessAutomaton.size());
				throw new ToolchainCanceledException(e, rti);
			}
		}
	}

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
	private void refineFinite(final LassoCheck<LETTER> lassoCheck) throws AutomataOperationCanceledException {
		mBenchmarkGenerator.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final TraceAbstractionRefinementEngine<LETTER> traceCheck;
		final NestedRun<LETTER, IPredicate> run;
		final LassoCheck<LETTER>.LassoCheckResult lcr = lassoCheck.getLassoCheckResult();
		if (lassoCheck.getLassoCheckResult().getStemFeasibility() == TraceCheckResult.INFEASIBLE) {
			// if both (stem and loop) are infeasible we take the smaller
			// one.
			final int stemSize = mCounterexample.getStem().getLength();
			final int loopSize = mCounterexample.getLoop().getLength();
			if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE && loopSize <= stemSize) {
				traceCheck = lassoCheck.getLoopCheck();
				run = mCounterexample.getLoop();
			} else {
				traceCheck = lassoCheck.getStemCheck();
				run = mCounterexample.getStem();
			}
		} else if (lcr.getLoopFeasibility() == TraceCheckResult.INFEASIBLE) {
			traceCheck = lassoCheck.getLoopCheck();
			run = mCounterexample.getLoop();
		} else {
			assert lcr.getConcatFeasibility() == TraceCheckResult.INFEASIBLE;
			traceCheck = lassoCheck.getConcatCheck();
			run = lassoCheck.getConcatenatedCounterexample();
		}
		// final BackwardCoveringInformation bci =
		// TraceCheckUtils.computeCoverageCapability(mServices, traceCheck, mLogger);
		// mBenchmarkGenerator.addBackwardCoveringInformationFinite(bci);

		// constructInterpolantAutomaton(traceCheck, run);
		mInterpolAutomaton = traceCheck.getInfeasibilityProof();
		// NestedLassoWord<LETTER> counter = utilFixedCe.getNestedLassoWord(
		// mAbstraction, counterName, 4);

		final IHoareTripleChecker htc = TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
				HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, traceCheck.getPredicateUnifier());

		final DeterministicInterpolantAutomaton<LETTER> determinized =
				new DeterministicInterpolantAutomaton<>(mServices, mCsToolkitWithRankVars, htc, mInterpolAutomaton,
						traceCheck.getPredicateUnifier(), false, false);
		final PowersetDeterminizer<LETTER, IPredicate> psd =
				new PowersetDeterminizer<>(determinized, true, mDefaultStateFactory);
		Difference<LETTER, IPredicate> diff = null;
		GeneralizedDifference<LETTER, IPredicate> gbaDiff = null;
		try {
			IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> gbaAbstraction;
			if (mAbstraction instanceof IGeneralizedNestedWordAutomaton) {
				gbaAbstraction = (IGeneralizedNestedWordAutomaton<LETTER, IPredicate>) mAbstraction;
				gbaDiff = new GeneralizedDifference<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, gbaAbstraction, determinized, psd);
			} else {
				diff = new Difference<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
						mAbstraction, determinized, psd, true);
			}
		} catch (final AutomataOperationCanceledException e) {
			mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
			throw e;
		} catch (final AutomataLibraryException e) {
			throw new AssertionError();
		} catch (final ToolchainCanceledException e) {
			mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
			throw e;
		}
		determinized.switchToReadonlyMode();
		if (mPref.dumpAutomata()) {
			final String filename =
					mIcfg.getIdentifier() + "_" + "interpolAutomatonUsedInRefinement" + mIteration + "after";
			writeAutomatonToFile(mServices, mInterpolAutomaton, mPref.dumpPath(), filename, mPref.getAutomataFormat(),
					"");
		}
		if (mConstructTermcompProof) {
			mTermcompProofBenchmark.reportFiniteModule(mIteration, mRefineBuchi.getInterpolAutomatonUsedInRefinement());
		}
		mMDBenchmark.reportTrivialModule(mIteration, mInterpolAutomaton.size());
		assert new InductivityCheck<>(mServices, mInterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(mCsToolkitWithRankVars, false)).getResult();
		// If no machine.conf file is in UltimateTest directory, then this flag is false
		// by default, NO machine.conf
		final boolean pldiDump = BenchmarkRecord.canDump();
		if (gbaDiff == null) {
			mAbstraction = diff.getResult();
			if (pldiDump) {
				BenchmarkRecord.addComplementAutomaton(mIteration, diff.getSecondComplemented().size(), 0);
			}
		} else {
			mAbstraction = gbaDiff.getResult();
			if (pldiDump) {
				BenchmarkRecord.addComplementAutomaton(mIteration, gbaDiff.getSecondComplemented().size(), 0);
			}
		}

		if (pldiDump) {
			dumpAutomatonInformation(determinized, true);
		}
		// UtilFixedCounterexample<LETTER, IPredicate> utilFixedCe = new UtilFixedCounterexample<>();
		// final String counterName = mIcfg.getIdentifier() + "_" + mName + "Abstraction";
		// try {
		// System.err.println("At iteration number " + mIteration);
		// utilFixedCe.checkAcceptance(new AutomataLibraryServices(mServices), mInterpolAutomaton, counterName, 5);
		// System.err.println("Difference automaton: ");
		// utilFixedCe.checkAcceptance(new AutomataLibraryServices(mServices), mAbstraction, counterName, 5);
		// } catch (AutomataLibraryException e1) {
		// // TODO Auto-generated catch block
		// e1.printStackTrace();
		// }
		assert automatonUsesISLPredicates(mAbstraction) : "used wrong StateFactory";
		mBenchmarkGenerator.addEdgeCheckerData(htc.getEdgeCheckerBenchmark());
		mBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
	}

	private void dumpAutomatonInformation(final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> automaton,
			final boolean isFinite) throws AutomataOperationCanceledException {
		final int numOfTrans =
				(new NumberOfTransitions<>(new AutomataLibraryServices(mServices), automaton)).getResult();
		final boolean includeDiff = BenchmarkRecord.includeDiffTransition();
		final int numOfTransOfDiff = includeDiff
				? (new NumberOfTransitions<>(new AutomataLibraryServices(mServices), mAbstraction)).getResult()
				: 0;
		if (isFinite) {
			BenchmarkRecord.addInterpolantOrDifferenceAutomaton(mIteration, automaton.size(), numOfTrans, 3,
					mAbstraction.size(), numOfTransOfDiff);
			return;
		}

		final boolean isSemiDeterministic =
				new IsSemiDeterministic<>(new AutomataLibraryServices(mServices), automaton).getResult();
		final boolean isDeterministic =
				new IsDeterministic<>(new AutomataLibraryServices(mServices), automaton).getResult();
		if (isDeterministic) {
			BenchmarkRecord.addInterpolantOrDifferenceAutomaton(mIteration, automaton.size(), numOfTrans, 2,
					mAbstraction.size(), numOfTransOfDiff);
		} else if (isSemiDeterministic) {
			BenchmarkRecord.addInterpolantOrDifferenceAutomaton(mIteration, automaton.size(), numOfTrans, 1,
					mAbstraction.size(), numOfTransOfDiff);
		} else {
			BenchmarkRecord.addInterpolantOrDifferenceAutomaton(mIteration, automaton.size(), numOfTrans, 0,
					mAbstraction.size(), numOfTransOfDiff);
		}
	}

	// protected void constructInterpolantAutomaton(final InterpolatingTraceCheck traceCheck,
	// final NestedRun<LETTER, IPredicate> run) throws AutomataOperationCanceledException {
	// final CanonicalInterpolantAutomatonBuilder<? extends Object, LETTER> iab =
	// new CanonicalInterpolantAutomatonBuilder<>(mServices, traceCheck.getIpp(), run.getStateSequence(),
	// new VpAlphabet<>(mAbstraction), mCsToolkitWithRankVars, mAbstraction.getStateFactory(),
	// mLogger, traceCheck.getPredicateUnifier(), run.getWord());
	// iab.analyze();
	// mInterpolAutomaton = iab.getResult();
	//
	// try {
	// assert new Accepts<>(new AutomataLibraryServices(mServices), mInterpolAutomaton, run.getWord())
	// .getResult() : "Interpolant automaton broken!";
	// } catch (final AutomataOperationCanceledException e) {
	// throw new ToolchainCanceledException(e, new RunningTaskInfo(getClass(), "checking acceptance"));
	// } catch (final AutomataLibraryException e) {
	// throw new AssertionError(e);
	// }
	// // assert((new BuchiAccepts<LETTER, IPredicate>(mInterpolAutomaton,
	// // mCounterexample.getNestedLassoWord())).getResult()) :
	// // "Interpolant automaton broken!";
	// assert new InductivityCheck<>(mServices, mInterpolAutomaton, false, true,
	// new IncrementalHoareTripleChecker(mCsToolkitWithRankVars)).getResult();
	// }

	private TerminationArgumentResult<IIcfgElement, Term> constructTAResult(
			final TerminationArgument terminationArgument, final IcfgLocation honda, final NestedWord<LETTER> stem,
			final NestedWord<LETTER> loop) {
		final RankingFunction rf = terminationArgument.getRankingFunction();
		final Collection<SupportingInvariant> si_list = terminationArgument.getSupportingInvariants();
		final Term[] supporting_invariants = new Term[si_list.size()];
		int i = 0;
		for (final SupportingInvariant si : terminationArgument.getSupportingInvariants()) {
			supporting_invariants[i] = si.asTerm(mCsToolkitWithRankVars.getManagedScript().getScript());
			++i;
		}
		final TerminationArgumentResult<IIcfgElement, Term> result = new TerminationArgumentResult<>(honda,
				Activator.PLUGIN_NAME, rf.asLexTerm(mCsToolkitWithRankVars.getManagedScript().getScript()),
				rf.getName(), supporting_invariants, mServices.getBacktranslationService(), Term.class);
		return result;
	}

	protected static void writeAutomatonToFile(final IUltimateServiceProvider services,
			final IAutomaton<?, IPredicate> automaton, final String path, final String filename, final Format format,
			final String message) {
		new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(services), "nwa",
				path + "/" + filename, format, message, automaton);
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
	public String generateLassoCheckIdentifier() {
		final String pureFilename = mIcfg.getIdentifier();
		return pureFilename + "_Iteration" + mIteration;
	}

	public BuchiCegarLoopBenchmarkGenerator getBenchmarkGenerator() {
		return mBenchmarkGenerator;
	}

	/**
	 * @return true iff run in LTL mode and results should be interpreted accordingly.
	 */
	public boolean isInLTLMode() {
		return mLTLMode;
	}

	private boolean automatonUsesISLPredicates(final INestedWordAutomaton<LETTER, IPredicate> nwa) {
		final Set<IPredicate> states = nwa.getStates();
		if (states.isEmpty()) {
			return true;
		}
		final IPredicate someState = states.iterator().next();
		return someState instanceof ISLPredicate;
	}

	private class SubtaskAdditionalLoopUnwinding extends TaskIdentifier {
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
