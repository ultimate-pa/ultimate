/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.AStarHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.LoopAccelerators;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier.ScoringMethod;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderMode;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade.OrderType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.AbstractionType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.IndependenceType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.CoinflipMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuseEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.McrInterpolantMethod;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.OrderOfErrorLocations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;

public final class TAPreferences {
	private static final boolean SEPARATE_VIOLATION_CHECK = true;
	private final boolean mInterprocedural;
	private final int mMaxIterations;
	private final int mWatchIteration;
	private final Artifact mArtifact;
	private final InterpolationTechnique mInterpolation;
	private final InterpolantAutomaton mInterpolantAutomaton;
	private final boolean mDumpAutomata;
	private final Format mAutomataFormat;
	private final String mDumpPath;
	private final InterpolantAutomatonEnhancement mDeterminiation;
	private final Minimization mMinimize;
	private final boolean mHoare;
	private final Concurrency mAutomataTypeConcurrency;
	private final HoareTripleChecks mHoareTripleChecks;
	@Reflected(excluded = true)
	private final IPreferenceProvider mPrefs;
	private final HoareAnnotationPositions mHoareAnnotationPositions;
	private final boolean mDumpOnlyReuseAutomata;
	private final int mLimitTraceHistogram;
	private final int mErrorLocTimeLimit;
	private final int mLimitPathProgramCount;
	private final boolean mCollectInterpolantStatistics;
	private final boolean mHeuristicEmptinessCheck;
	private final AStarHeuristic mHeuristicEmptinessCheckAStarHeuristic;
	private final Integer mHeuristicEmptinessCheckAStarHeuristicRandomSeed;
	private final ScoringMethod mHeuristicEmptinessCheckSmtFeatureScoringMethod;
	private final boolean mSMTFeatureExtraction;
	private final String mSMTFeatureExtractionDumpPath;
	private final boolean mOverrideInterpolantAutomaton;
	private final McrInterpolantMethod mMcrInterpolantMethod;

	private final IndependenceSettings[] mPorIndependenceSettings;
	private final IndependenceSettings mLbeIndependenceSettings;

	public enum Artifact {
		ABSTRACTION, INTERPOLANT_AUTOMATON, NEG_INTERPOLANT_AUTOMATON, RCFG
	}

	public enum InterpolantAutomatonEnhancement {
		NONE, EAGER, EAGER_CONSERVATIVE, NO_SECOND_CHANCE, PREDICATE_ABSTRACTION, PREDICATE_ABSTRACTION_CONSERVATIVE,
		PREDICATE_ABSTRACTION_CANNIBALIZE,
	}

	public enum Concurrency {
		FINITE_AUTOMATA, PETRI_NET, PARTIAL_ORDER_FA
	}

	public enum LooperCheck {
		SYNTACTIC, SEMANTIC
	}

	public TAPreferences(final IUltimateServiceProvider services) {

		mPrefs = services.getPreferenceProvider(Activator.PLUGIN_ID);

		mInterprocedural = mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_INTERPROCEDURAL);

		mMaxIterations = mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_USERLIMIT_ITERATIONS);
		mWatchIteration = mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_WATCHITERATION);

		mArtifact = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ARTIFACT, Artifact.class);

		mHoare = mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_HOARE);

		mHoareAnnotationPositions = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_HOARE_POSITIONS,
				HoareAnnotationPositions.class);

		mInterpolation = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS,
				InterpolationTechnique.class);

		mInterpolantAutomaton = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANT_AUTOMATON,
				InterpolantAutomaton.class);

		mDumpAutomata = mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_DUMPAUTOMATA);

		mAutomataFormat = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_AUTOMATAFORMAT, Format.class);

		mDumpPath = mPrefs.getString(TraceAbstractionPreferenceInitializer.LABEL_DUMPPATH);
		mDumpOnlyReuseAutomata = mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_DUMP_ONLY_REUSE);

		mDeterminiation = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANT_AUTOMATON_ENHANCEMENT,
				InterpolantAutomatonEnhancement.class);

		mHoareTripleChecks = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_HOARE_TRIPLE_CHECKS,
				HoareTripleChecks.class);

		mMinimize = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_MINIMIZE, Minimization.class);

		mAutomataTypeConcurrency =
				mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_CONCURRENCY, Concurrency.class);

		mLimitTraceHistogram = mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_USERLIMIT_TRACE_HISTOGRAM);
		mErrorLocTimeLimit = mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_USERLIMIT_TIME);
		mLimitPathProgramCount = mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_USERLIMIT_PATH_PROGRAM);

		mCollectInterpolantStatistics =
				mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_COMPUTE_INTERPOLANT_SEQUENCE_STATISTICS);

		if (artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
			throw new IllegalArgumentException(
					"Show negated interpolant" + "automaton not possible when using difference.");
		}

		if (mWatchIteration == 0
				&& (artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON || artifact() == Artifact.INTERPOLANT_AUTOMATON)) {
			throw new IllegalArgumentException("There is no interpolant" + "automaton in iteration 0.");
		}

		mHeuristicEmptinessCheck =
				mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_HEURISTIC_EMPTINESS_CHECK);

		mHeuristicEmptinessCheckAStarHeuristic =
				mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_HEURISTIC_EMPTINESS_CHECK_ASTAR_HEURISTIC,
						AStarHeuristic.class);

		mHeuristicEmptinessCheckSmtFeatureScoringMethod =
				mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_HEURISTIC_EMPTINESS_CHECK_SCORING_METHOD,
						ScoringMethod.class);

		mHeuristicEmptinessCheckAStarHeuristicRandomSeed = mPrefs.getInt(
				TraceAbstractionPreferenceInitializer.LABEL_HEURISTIC_EMPTINESS_CHECK_ASTAR_RANDOM_HEURISTIC_SEED);

		mSMTFeatureExtraction = mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_SMT_FEATURE_EXTRACTION);
		mSMTFeatureExtractionDumpPath =
				mPrefs.getString(TraceAbstractionPreferenceInitializer.LABEL_SMT_FEATURE_EXTRACTION_DUMP_PATH);
		mOverrideInterpolantAutomaton =
				mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_OVERRIDE_INTERPOLANT_AUTOMATON);
		mMcrInterpolantMethod = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_MCR_INTERPOLANT_METHOD,
				McrInterpolantMethod.class);

		mPorIndependenceSettings = new IndependenceSettings[getNumberOfIndependenceRelations()];
		mLbeIndependenceSettings = new IndependenceSettings(
				mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INDEPENDENCE_PLBE, IndependenceType.class),
				AbstractionType.NONE /* currently hard-coded; will be changed for repeated Petri net LBE */,
				false /* currently hard-coded; will be changed for repeated Petri net LBE */,
				mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_SEMICOMM_PLBE),
				IndependenceSettings.DEFAULT_SOLVER /* currently ignored; not exposed as setting */,
				IndependenceSettings.DEFAULT_SOLVER_TIMEOUT /* currently ignored; not exposed as setting */);
	}

	/**
	 * @return The interprocedural.
	 */
	public boolean interprocedural() {
		return mInterprocedural;
	}

	public boolean stopAfterFirstViolation() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_STOP_AFTER_FIRST_VIOLATION);
	}

	public OrderOfErrorLocations getOrderOfErrorLocations() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ORDER_OF_ERROR_LOCATIONS,
				OrderOfErrorLocations.class);
	}

	public boolean readInitialProof() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_READ_INITIAL_PROOF_ASSERTIONS_FROM_FILE);
	}

	public FloydHoareAutomataReuse getFloydHoareAutomataReuse() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_FLOYD_HOARE_AUTOMATA_REUSE,
				FloydHoareAutomataReuse.class);
	}

	public FloydHoareAutomataReuseEnhancement getFloydHoareAutomataReuseEnhancement() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT,
				FloydHoareAutomataReuseEnhancement.class);
	}

	public SolverMode solverMode() {
		return mPrefs.getEnum(RcfgPreferenceInitializer.LABEL_SOLVER, SolverMode.class);
	}

	public String commandExternalSolver() {
		return mPrefs.getString(RcfgPreferenceInitializer.LABEL_EXT_SOLVER_COMMAND);
	}

	public Logics logicForExternalSolver() {
		return Logics.valueOf(mPrefs.getString(RcfgPreferenceInitializer.LABEL_EXT_SOLVER_LOGIC));
	}

	public boolean dumpSmtScriptToFile() {
		return mPrefs.getBoolean(RcfgPreferenceInitializer.LABEL_DUMP_TO_FILE);
	}

	public boolean compressDumpedSmtScript() {
		return mPrefs.getBoolean(RcfgPreferenceInitializer.LABEL_COMPRESS_SMT_DUMP_FILE);
	}

	public String pathOfDumpedScript() {
		return mPrefs.getString(RcfgPreferenceInitializer.LABEL_DUMP_PATH);
	}

	/**
	 * @return The maxIterations.
	 */
	public int maxIterations() {
		return mMaxIterations;
	}

	/**
	 * @return The prefObservedIteration.
	 */
	public int watchIteration() {
		return mWatchIteration;
	}

	/**
	 * @return The artifact.
	 */
	public Artifact artifact() {
		return mArtifact;
	}

	public boolean useSeparateSolverForTracechecks() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_SEPARATE_SOLVER);
	}

	/**
	 * @return The interpolation technique.
	 */
	public InterpolationTechnique interpolation() {
		return mInterpolation;
	}

	/**
	 * @return The interpolant automaton.
	 */
	public InterpolantAutomaton interpolantAutomaton() {
		return mInterpolantAutomaton;
	}

	/**
	 * @return The dump automata flag.
	 */
	public boolean dumpAutomata() {
		return mDumpAutomata && !mDumpOnlyReuseAutomata;
	}

	public Format getAutomataFormat() {
		return mAutomataFormat;
	}

	/**
	 * @return The dump path.
	 */
	public String dumpPath() {
		return mDumpPath;
	}

	public boolean dumpOnlyReuseAutomata() {
		return mDumpAutomata && mDumpOnlyReuseAutomata;
	}

	/**
	 * @return The determinization.
	 */
	public InterpolantAutomatonEnhancement interpolantAutomatonEnhancement() {
		return mDeterminiation;
	}

	public HoareTripleChecks getHoareTripleChecks() {
		return mHoareTripleChecks;
	}

	/**
	 * @return The difference.
	 */
	public boolean differenceSenwa() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_DIFFERENCE_SENWA);
	}

	/**
	 * @return The minimization.
	 */
	public Minimization getMinimization() {
		return mMinimize;
	}

	public Concurrency getAutomataTypeConcurrency() {
		return mAutomataTypeConcurrency;
	}

	public boolean computeHoareAnnotation() {
		return mHoare;
	}

	public HoareAnnotationPositions getHoareAnnotationPositions() {
		return mHoareAnnotationPositions;
	}

	public static boolean separateViolationCheck() {
		return SEPARATE_VIOLATION_CHECK;
	}

	public boolean cutOffRequiresSameTransition() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_CUTOFF);
	}

	public boolean unfoldingToNet() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_BACKFOLDING);
	}

	public EventOrderEnum eventOrder() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_CONFIGURATION_ORDER, EventOrderEnum.class);
	}

	public LooperCheck looperCheck() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_LOOPER_CHECK_PETRI, LooperCheck.class);
	}

	public boolean applyOneShotLbe() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_PETRI_LBE_ONESHOT);
	}

	public boolean applyOneShotPOR() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_POR_ONESHOT);
	}

	public PartialOrderMode getPartialOrderMode() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_POR_MODE, PartialOrderMode.class);
	}

	public boolean dumpIndependenceScript() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_DUMP_INDEPENDENCE_SCRIPT);
	}

	public String independenceScriptDumpPath() {
		return mPrefs.getString(TraceAbstractionPreferenceInitializer.LABEL_INDEPENDENCE_SCRIPT_DUMP_PATH);
	}

	public OrderType getDfsOrderType() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_POR_DFS_ORDER, OrderType.class);
	}

	public long getDfsOrderSeed() {
		return mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_POR_DFS_RANDOM_SEED);
	}

	public CoinflipMode useCoinflip() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_POR_COINFLIP_MODE, CoinflipMode.class);
	}

	public double getCoinflipProbability(final int iteration) {
		final int basicProbability = mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_POR_COINFLIP_PROB);
		final int probabilityIncrement =
				mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_POR_COINFLIP_INCREMENT);
		final int probability = Integer.min(100, basicProbability + iteration * probabilityIncrement);
		return probability / 100.0D;
	}

	public int coinflipSeed() {
		return mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_POR_COINFLIP_SEED);
	}

	public int getNumberOfIndependenceRelations() {
		return mPrefs.getInt(TraceAbstractionPreferenceInitializer.LABEL_POR_NUM_INDEPENDENCE);
	}

	public IndependenceSettings porIndependenceSettings(final int index) {
		if (index < 0 || index >= getNumberOfIndependenceRelations()) {
			throw new IllegalArgumentException(
					"Index out of range: " + index + " not between 0 and " + getNumberOfIndependenceRelations());
		}
		if (mPorIndependenceSettings[index] == null) {
			mPorIndependenceSettings[index] = new IndependenceSettings(
					mPrefs.getEnum(getLabel(TraceAbstractionPreferenceInitializer.LABEL_INDEPENDENCE_POR, index),
							IndependenceSettings.DEFAULT_INDEPENDENCE_TYPE, IndependenceType.class),
					mPrefs.getEnum(getLabel(TraceAbstractionPreferenceInitializer.LABEL_POR_ABSTRACTION, index),
							IndependenceSettings.DEFAULT_ABSTRACTION_TYPE, AbstractionType.class),
					mPrefs.getBoolean(getLabel(TraceAbstractionPreferenceInitializer.LABEL_COND_POR, index),
							IndependenceSettings.DEFAULT_USE_CONDITIONAL),
					mPrefs.getBoolean(getLabel(TraceAbstractionPreferenceInitializer.LABEL_SEMICOMM_POR, index),
							IndependenceSettings.DEFAULT_USE_SEMICOMMUTATIVITY),
					mPrefs.getEnum(getLabel(TraceAbstractionPreferenceInitializer.LABEL_INDEPENDENCE_SOLVER_POR, index),
							IndependenceSettings.DEFAULT_SOLVER, ExternalSolver.class),
					mPrefs.getLong(getLabel(TraceAbstractionPreferenceInitializer.LABEL_INDEPENDENCE_SOLVER_TIMEOUT_POR,
							index), IndependenceSettings.DEFAULT_SOLVER_TIMEOUT));
		}
		return mPorIndependenceSettings[index];
	}

	private static String getLabel(final String label, final int index) {
		return TraceAbstractionPreferenceInitializer.getSuffixedLabel(label, index);
	}

	public IndependenceSettings lbeIndependenceSettings() {
		return mLbeIndependenceSettings;
	}

	public SimplificationTechnique getSimplificationTechnique() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_SIMPLIFICATION_TECHNIQUE,
				SimplificationTechnique.class);
	}

	public XnfConversionTechnique getXnfConversionTechnique() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_XNF_CONVERSION_TECHNIQUE,
				XnfConversionTechnique.class);
	}

	public boolean fakeNonIncrementalSolver() {
		return mPrefs.getBoolean(RcfgPreferenceInitializer.LABEL_FAKE_NON_INCREMENTAL_SCRIPT);
	}

	public RefinementStrategy getRefinementStrategy() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_REFINEMENT_STRATEGY,
				RefinementStrategy.class);
	}

	public RefinementStrategy getMcrRefinementStrategy() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_MCR_REFINEMENT_STRATEGY,
				RefinementStrategy.class);
	}

	public RefinementStrategy getAcceleratedInterpolationRefinementStrategy() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ACIP_REFINEMENT_STRATEGY,
				RefinementStrategy.class);
	}

	public RefinementStrategyExceptionBlacklist getRefinementStrategyExceptionSpecification() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST,
				RefinementStrategyExceptionBlacklist.class);
	}

	public boolean hasLimitTraceHistogram() {
		return getLimitTraceHistogram() > 0;
	}

	public int getLimitTraceHistogram() {
		return mLimitTraceHistogram;
	}

	public boolean hasErrorLocTimeLimit() {
		return mErrorLocTimeLimit > 0;
	}

	public LoopAccelerators getLoopAccelerationTechnique() {
		return mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ACCELINTERPOL_LOOPACCELERATION_TECHNIQUE,
				LoopAccelerators.class);
	}

	/**
	 * @return A positive integer that specifies a time limit in seconds for the analysis of an error location or zero
	 *         if no limit is set.
	 */
	public int getErrorLocTimeLimit() {
		return mErrorLocTimeLimit;
	}

	public boolean hasLimitPathProgramCount() {
		return mLimitPathProgramCount > 0;
	}

	public int getLimitPathProgramCount() {
		return mLimitPathProgramCount;
	}

	public boolean collectInterpolantStatistics() {
		return mCollectInterpolantStatistics;
	}

	public boolean useHeuristicEmptinessCheck() {
		return mHeuristicEmptinessCheck;
	}

	public ScoringMethod getHeuristicEmptinessCheckScoringMethod() {
		return mHeuristicEmptinessCheckSmtFeatureScoringMethod;
	}

	public AStarHeuristic getHeuristicEmptinessCheckAStarHeuristic() {
		return mHeuristicEmptinessCheckAStarHeuristic;
	}

	public Integer getHeuristicEmptinessCheckAStarHeuristicRandomSeed() {
		return mHeuristicEmptinessCheckAStarHeuristicRandomSeed;
	}

	public boolean useSMTFeatureExtraction() {
		return mSMTFeatureExtraction;
	}

	public String getSMTFeatureExtractionDumpPath() {
		return mSMTFeatureExtractionDumpPath;
	}

	public boolean overrideInterpolantAutomaton() {
		return mOverrideInterpolantAutomaton;
	}

	public McrInterpolantMethod getMcrInterpolantMethod() {
		return mMcrInterpolantMethod;
	}

	public boolean owickiGriesCoveringSimplification() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_OG_COVERING_SIMPLIFICATION);
	}

	public boolean owickiGriesHittingSets() {
		return mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_OG_HITTING_SET_OPTIMIZATION);
	}
}
