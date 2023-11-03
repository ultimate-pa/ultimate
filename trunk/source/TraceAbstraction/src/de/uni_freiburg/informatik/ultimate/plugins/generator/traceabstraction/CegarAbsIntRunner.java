/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.CachingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.Reason;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.AbsIntNonSmtInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.AbsIntStraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.AbsIntTotalInterpolationAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.AbsIntHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AbstractInterpretationMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.weakener.AbsIntPredicateInterpolantSequenceWeakener;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.statistics.IKeyedStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class CegarAbsIntRunner<LETTER extends IIcfgTransition<?>> {

	private static final boolean USE_INTERPOLANT_WEAKENER = true;

	private static final boolean DEBUG_PRINT_TRACE = false;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final CfgSmtToolkit mCsToolkit;
	private final IIcfg<?> mRoot;

	private final AbstractInterpretationMode mMode;
	private final boolean mAlwaysRefine;
	private final PathProgramCache<LETTER> mPathProgramCache;
	private final TAPreferences mTaPreferences;
	private final AbsIntStatisticsGenerator mStats;

	private final AbsIntCurrentIteration<?> mCurrentIteration;
	private final IPredicateUnifier mPredicateUnifierSmt;

	public CegarAbsIntRunner(final IUltimateServiceProvider services, final IIcfg<?> root,
			final PathProgramCache<LETTER> pathProgramCache, final TAPreferences taPrefs,
			final IRun<LETTER, ?> currentCex, final IPredicateUnifier unifier) {
		mStats = new AbsIntStatisticsGenerator();
		mServices = services;
		mTaPreferences = taPrefs;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mRoot = root;
		mPathProgramCache = pathProgramCache;
		mCsToolkit = root.getCfgSmtToolkit();
		mPredicateUnifierSmt = Objects.requireNonNull(unifier);

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mAlwaysRefine = prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_ABSINT_ALWAYS_REFINE);
		mMode = prefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ABSINT_MODE,
				AbstractInterpretationMode.class);
		checkSettings();
		mCurrentIteration = generateFixpoints(currentCex);
		if (hasShownInfeasibility()) {
			mStats.increment(AbsIntStats.WAS_STRONG);
		}
	}

	/**
	 * Generate fixpoints for each program location of a path program represented by the current counterexample in the
	 * current abstraction.
	 *
	 * Do not run if
	 * <ul>
	 * <li>We have already analyzed the exact same path program.
	 * <li>The path program does not contain any loops.
	 * </ul>
	 */
	private AbsIntCurrentIteration<?> generateFixpoints(final IRun<LETTER, ?> cex) {
		assert cex != null : "Cannot run AI on empty counterexample";

		if (!mRoot.getLocationClass().equals(BoogieIcfgLocation.class)) {
			// TODO: AI only supports BoogieIcfgLocations and Codeblocks atm, so die if this is not the type presented.
			throw new UnsupportedOperationException(
					"AbsInt only supports BoogieIcfgLocations and Codeblocks at the moment");
		}
		if (IcfgUtils.isConcurrent(mRoot)) {
			throw new UnsupportedOperationException("AbsInt currently does not support concurrent programs");
		}

		if (mMode == AbstractInterpretationMode.NONE) {
			return null;
		}

		mStats.resume(AbsIntStats.TIME);
		try {

			final int seen = mPathProgramCache.getPathProgramCount(cex);
			if (seen > 1) {
				mLogger.info("Skipping current iteration for AI because we have already analyzed this path program");
				return null;
			}
			final Set<LETTER> pathProgramSet = cex.getWord().asSet();
			if (!containsLoop(pathProgramSet)
					&& mTaPreferences.getRefinementStrategy() != RefinementStrategy.TOOTHLESS_TAIPAN) {
				mLogger.info("Skipping current iteration for AI because the path program does not contain any loops");
				return null;
			}

			final int currentAbsIntIter = mStats.increment(AbsIntStats.ITERATIONS) + 1;

			// allow for 20% of the remaining time
			// final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
			// allow for all the remaining time
			final IProgressAwareTimer timer = mServices.getProgressMonitorService();
			mLogger.info("Running AI on error trace of length " + cex.getLength());
			if (DEBUG_PRINT_TRACE) {
				mLogger.info(String.join(", ", pathProgramSet.stream().map(LETTER::hashCode).sorted()
						.map(a -> '[' + String.valueOf(a) + ']').collect(Collectors.toList())));
				mLogger.info("Trace:");
				for (final LETTER trans : cex.getWord().asList()) {
					mLogger.info("[" + trans.hashCode() + "] " + trans);
				}
			}

			final PathProgram pp =
					PathProgram.constructPathProgram("absint-pp-iter-" + currentAbsIntIter, mRoot, pathProgramSet)
							.getPathProgram();

			@SuppressWarnings("unchecked")
			final IAbstractInterpretationResult<?, LETTER, ?> result =
					(IAbstractInterpretationResult<?, LETTER, ?>) AbstractInterpreter.runWithoutTimeoutAndResults(pp,
							timer, mServices);
			if (result == null) {
				return null;
			}
			return new AbsIntCurrentIteration<>(cex, result, pp);

		} finally {
			mStats.stop(AbsIntStats.TIME);
		}
	}

	/**
	 *
	 * @return true iff abstract interpretation was strong enough to prove infeasibility of the current counterexample.
	 */
	public boolean hasShownInfeasibility() {
		return mMode != AbstractInterpretationMode.NONE && mCurrentIteration != null
				&& !mCurrentIteration.hasReachedError();
	}

	public boolean isDisabled() {
		return mMode == AbstractInterpretationMode.NONE;
	}

	public CachingHoareTripleChecker getHoareTripleChecker() {
		if (mCurrentIteration == null) {
			throw createNoFixpointsException();
		}
		return mCurrentIteration.getHoareTripleChecker();
	}

	public IPredicateUnifier getPredicateUnifier() {
		if (mCurrentIteration == null) {
			throw createNoFixpointsException();
		}
		return mCurrentIteration.getPredicateUnifier();
	}

	public IInterpolatingTraceCheck<LETTER> getInterpolantGenerator() {
		if (mCurrentIteration == null) {
			return new AbsIntFailedInterpolantGenerator<>(mPredicateUnifierSmt, null, ItpErrorStatus.ALGORITHM_FAILED,
					createNoFixpointsException());
		}
		return mCurrentIteration.getInterpolantGenerator();
	}

	public IInterpolantAutomatonBuilder<LETTER, IPredicate> createInterpolantAutomatonBuilder(
			final IPredicateUnifier predicateUnifier, final INestedWordAutomaton<LETTER, IPredicate> abstraction,
			final IRun<LETTER, ?> currentCex, final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		if (mCurrentIteration == null) {
			throw createNoFixpointsException();
		}

		mStats.resume(AbsIntStats.TIME);
		try {
			mLogger.info("Constructing AI automaton with mode " + mMode);
			final IInterpolantAutomatonBuilder<LETTER, IPredicate> aiInterpolAutomatonBuilder;
			final SimplificationTechnique simplificationTechnique = mTaPreferences.getSimplificationTechnique();
			final XnfConversionTechnique xnfConversionTechnique = mTaPreferences.getXnfConversionTechnique();
			switch (mMode) {
			case NONE:
				throw new AssertionError("Mode should have been checked earlier");
			case USE_PATH_PROGRAM:
				aiInterpolAutomatonBuilder = new AbsIntNonSmtInterpolantAutomatonBuilder<>(mServices, abstraction,
						predicateUnifier, mCsToolkit.getManagedScript(), mRoot.getCfgSmtToolkit().getSymbolTable(),
						currentCex, simplificationTechnique, xnfConversionTechnique, emptyStackFactory);
				break;
			case USE_PREDICATES:
				aiInterpolAutomatonBuilder = new AbsIntStraightLineInterpolantAutomatonBuilder<>(mServices, abstraction,
						mCurrentIteration.getResult(), predicateUnifier, mCsToolkit, currentCex,
						simplificationTechnique, xnfConversionTechnique, mRoot.getCfgSmtToolkit().getSymbolTable(),
						emptyStackFactory);
				break;
			case USE_CANONICAL:
				throw new UnsupportedOperationException(
						"Canonical interpolant automaton generation not yet implemented.");
			case USE_TOTAL:
				aiInterpolAutomatonBuilder = new AbsIntTotalInterpolationAutomatonBuilder<>(mServices, abstraction,
						mCurrentIteration.getResult(), predicateUnifier, mCsToolkit, currentCex,
						mRoot.getCfgSmtToolkit().getSymbolTable(), simplificationTechnique, xnfConversionTechnique,
						emptyStackFactory);
				break;
			default:
				throw new UnsupportedOperationException("AI mode " + mMode + " not yet implemented");
			}
			return aiInterpolAutomatonBuilder;
		} finally {
			mStats.stop(AbsIntStats.TIME);
		}
	}

	public IStatisticsDataProvider getStatistics() {
		return mStats;
	}

	private void checkSettings() {
		if (mMode == AbstractInterpretationMode.USE_PATH_PROGRAM && mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANT_AUTOMATON_ENHANCEMENT,
						InterpolantAutomatonEnhancement.class) != InterpolantAutomatonEnhancement.NONE) {
			throw new IllegalArgumentException("If using \"" + TraceAbstractionPreferenceInitializer.LABEL_ABSINT_MODE
					+ "\"=" + AbstractInterpretationMode.USE_PATH_PROGRAM + " you also have to use \""
					+ TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANT_AUTOMATON_ENHANCEMENT + "\"="
					+ InterpolantAutomatonEnhancement.NONE);
		}
		if (mMode == AbstractInterpretationMode.NONE && mAlwaysRefine) {
			throw new IllegalArgumentException("If using \"" + TraceAbstractionPreferenceInitializer.LABEL_ABSINT_MODE
					+ "\"=" + AbstractInterpretationMode.NONE + " you cannot use \""
					+ TraceAbstractionPreferenceInitializer.LABEL_ABSINT_ALWAYS_REFINE + "\"=true");
		}
	}

	private boolean containsLoop(final Set<LETTER> pathProgramSet) {
		final Set<IcfgLocation> programPoints = new HashSet<>();
		return pathProgramSet.stream().anyMatch(a -> !programPoints.add(a.getTarget()));
	}

	private static UnsupportedOperationException createNoFixpointsException() {
		return new UnsupportedOperationException(
				"AbsInt can only provide a hoare triple checker if it generated fixpoints");
	}

	public static final class AbsIntStatisticsGenerator implements IStatisticsDataProvider {

		private static final StatisticsType<AbsIntStats> TYPE = new StatisticsType<>(AbsIntStats.class);

		private final Map<AbsIntStats, Integer> mIntCounters = new EnumMap<>(AbsIntStats.class);
		private final Map<AbsIntStats, Double> mRatioSum = new EnumMap<>(AbsIntStats.class);
		private final Map<AbsIntStats, Integer> mRatioFrequency = new EnumMap<>(AbsIntStats.class);
		private final Benchmark mStopwatches = new Benchmark();

		@Override
		public IStatisticsType getBenchmarkType() {
			return TYPE;
		}

		@Override
		public Collection<String> getKeys() {
			return TYPE.getKeys();
		}

		@Override
		public Object getValue(final String keyName) {
			return getValue(AbsIntStats.valueOf(keyName));
		}

		public Object getValue(final AbsIntStats key) {
			switch (key.getType()) {
			case COUNTER:
				return mIntCounters.getOrDefault(key, 0);
			case RATIO:
				return mRatioSum.getOrDefault(key, 0.0) / (double) mRatioFrequency.getOrDefault(key, 1);
			case TIMER:
				return (long) mStopwatches.getElapsedTime(key.getName(), TimeUnit.NANOSECONDS);
			default:
				throw new UnsupportedOperationException("Unsupported key type " + key.getType());
			}
		}

		public int increment(final AbsIntStats key) {
			return add(key, 1);
		}

		public int add(final AbsIntStats key, final int summand) {
			assert key.getType() == KeyType.COUNTER;
			final int oldOrDefaultValue = mIntCounters.getOrDefault(key, 0);
			final Integer oldValue = mIntCounters.put(key, oldOrDefaultValue + summand);
			if (oldValue == null) {
				return 0;
			}
			return oldValue;
		}

		public void addRatio(final AbsIntStats key, final double ratio) {
			assert key.getType() == KeyType.RATIO;
			mRatioSum.put(key, mRatioSum.getOrDefault(key, 0.0) + ratio);
			mRatioFrequency.put(key, mRatioFrequency.getOrDefault(key, 0) + 1);
		}

		/**
		 * Start or restart a stopwatch
		 */
		public void start(final AbsIntStats key) {
			assert key.getType() == KeyType.TIMER;
			mStopwatches.start(key.getName());
		}

		/**
		 * Stop or pause a stopwatch
		 */
		public void stop(final AbsIntStats key) {
			assert key.getType() == KeyType.TIMER;
			mStopwatches.stop(key.getName());
		}

		/**
		 * Resume or unpause a stopped stopwatch. If the watch is not started, it will be started.
		 */
		public void resume(final AbsIntStats key) {
			assert key.getType() == KeyType.TIMER;
			mStopwatches.register(key.getName());
			mStopwatches.unpause(key.getName());
		}
	}

	public enum AbsIntStats implements IKeyedStatisticsElement {

		TIME(KeyType.TIMER),

		ITERATIONS(KeyType.COUNTER),

		WAS_STRONG(KeyType.COUNTER),

		WEAKENING_RATIO(KeyType.RATIO),

		AVG_VARS_REMOVED_DURING_WEAKENING(KeyType.RATIO),

		AVG_WEAKENED_CONJUNCTS(KeyType.RATIO);

		private final KeyType mType;

		AbsIntStats(final KeyType type) {
			mType = type;
		}

		@Override
		public KeyType getType() {
			return mType;
		}

		@Override
		public String getName() {
			return name();
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 * @param <STATE>
	 */
	private final class AbsIntCurrentIteration<STATE extends IAbstractState<STATE>> {
		private final IRun<LETTER, ?> mCex;
		private final IAbstractInterpretationResult<STATE, LETTER, ?> mResult;

		private IInterpolatingTraceCheck<LETTER> mInterpolantGenerator;
		private CachingHoareTripleChecker mHtc;
		private final AbsIntPredicate<STATE> mFalsePredicate;
		private final AbsIntPredicate<STATE> mTruePredicate;
		private final IPredicateUnifier mPredicateUnifierAbsInt;
		private final PathProgram mPathProgram;

		public AbsIntCurrentIteration(final IRun<LETTER, ?> cex,
				final IAbstractInterpretationResult<STATE, LETTER, ?> result, final PathProgram pathprogram) {
			mPathProgram = Objects.requireNonNull(pathprogram);
			mCex = Objects.requireNonNull(cex);
			mResult = Objects.requireNonNull(result);
			mFalsePredicate = new AbsIntPredicate<>(mPredicateUnifierSmt.getFalsePredicate(),
					mResult.getUsedDomain().createBottomState());
			mTruePredicate = new AbsIntPredicate<>(mPredicateUnifierSmt.getTruePredicate(),
					mResult.getUsedDomain().createTopState());
			mPredicateUnifierAbsInt = new AbsIntPredicateUnifier<>(mLogger, mServices, mCsToolkit.getManagedScript(),
					mPredicateUnifierSmt.getPredicateFactory(), mCsToolkit.getSymbolTable(),
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, mFalsePredicate, mTruePredicate);
		}

		public IPredicateUnifier getPredicateUnifier() {
			return mPredicateUnifierAbsInt;
		}

		public IAbstractInterpretationResult<STATE, LETTER, ?> getResult() {
			return mResult;
		}

		public boolean hasReachedError() {
			return mResult.hasReachedError();
		}

		public CachingHoareTripleChecker getHoareTripleChecker() {
			if (mHtc == null) {
				mHtc = createHoareTripleChecker(false);
			}
			return mHtc;
		}

		private CachingHoareTripleChecker createHoareTripleChecker(final boolean onlyAbsInt) {
			final IHoareTripleChecker htc = new AbsIntHoareTripleChecker<>(mLogger, mServices, mResult.getUsedDomain(),
					mResult.getUsedVariableProvider(), mPredicateUnifierAbsInt, mCsToolkit, onlyAbsInt);
			return new CachingHoareTripleChecker(mServices, htc, mPredicateUnifierAbsInt);
		}

		public IInterpolatingTraceCheck<LETTER> getInterpolantGenerator() {
			if (mInterpolantGenerator == null) {
				mInterpolantGenerator = createInterpolantGenerator();
			}
			return mInterpolantGenerator;
		}

		private IInterpolatingTraceCheck<LETTER> createInterpolantGenerator() {
			if (mResult.hasReachedError()) {
				// analysis was not strong enough
				return new AbsIntFailedInterpolantGenerator<>(mPredicateUnifierAbsInt, mCex.getWord(),
						ItpErrorStatus.ALGORITHM_FAILED, null);
			}
			// we were strong enough!
			final Word<LETTER> word = mCex.getWord();
			try {
				mLogger.info("Generating AbsInt predicates");
				final List<LETTER> ppTrace = constructTraceFromWord(word, mPathProgram);
				final List<AbsIntPredicate<STATE>> nonUnifiedPredicates = generateAbsIntPredicates(ppTrace);
				assert isInductive(ppTrace, nonUnifiedPredicates,
						createHoareTripleChecker(true)) : "Sequence of interpolants not inductive (before weakening)!";

				final List<AbsIntPredicate<STATE>> weakenedPredicates;
				if (USE_INTERPOLANT_WEAKENER) {
					final CachingHoareTripleChecker absIntOnlyHtc = createHoareTripleChecker(true);
					weakenedPredicates = weakenPredicates(nonUnifiedPredicates, ppTrace, absIntOnlyHtc);
					assert isInductive(ppTrace, weakenedPredicates,
							absIntOnlyHtc) : "Sequence of interpolants not inductive (after weakening)!";
				} else {
					weakenedPredicates = nonUnifiedPredicates;
				}
				mLogger.info("Unifying AI predicates");
				final List<AbsIntPredicate<STATE>> interpolants = unifyPredicates(weakenedPredicates);
				mLogger.info("We unified " + weakenedPredicates.size() + " AI predicates to " + interpolants.size());
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Interpolant sequence:");
					mLogger.debug(interpolants);
				}
				assert word.length() - 1 == interpolants.size() : "Word has length " + word.length()
						+ " but interpolant sequence has length " + interpolants.size();
				assert isInductive(ppTrace, interpolants,
						getHoareTripleChecker()) : "Sequence of interpolants not inductive (after unification)";
				mLogger.info("Finished generation of AbsInt predicates");
				return new AbsIntInterpolantGenerator<>(mPredicateUnifierAbsInt, mCex.getWord(),
						interpolants.toArray(new IPredicate[interpolants.size()]), getHoareTripleChecker(),
						mTruePredicate, mFalsePredicate);
			} catch (final ToolchainCanceledException tce) {
				tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), "generating AI predicates"));
				throw tce;
			}
		}

		private List<AbsIntPredicate<STATE>> unifyPredicates(final List<AbsIntPredicate<STATE>> weakenedPredicates) {
			return weakenedPredicates.stream()
					.map(a -> getPredicateFromStates(a.getAbstractStates(), mCsToolkit.getManagedScript().getScript()))
					.collect(Collectors.toList());
		}

		private List<AbsIntPredicate<STATE>> weakenPredicates(final List<AbsIntPredicate<STATE>> nonUnifiedPredicates,
				final List<LETTER> ppTrace, final IHoareTripleChecker htc) {
			return new AbsIntPredicateInterpolantSequenceWeakener<>(mLogger, htc, nonUnifiedPredicates, ppTrace,
					mTruePredicate, mFalsePredicate, mCsToolkit.getManagedScript().getScript(),
					mPredicateUnifierAbsInt.getPredicateFactory(), mStats).getResult();
		}

		@SuppressWarnings("unchecked")
		private List<LETTER> constructTraceFromWord(final Word<LETTER> word, final PathProgram pathProgram) {
			final Map<LETTER, LETTER> wordLetter2PathProgramLetter = new HashMap<>();
			final IcfgEdgeIterator iter = new IcfgEdgeIterator(pathProgram);
			while (iter.hasNext()) {
				final IcfgEdge current = iter.next();
				wordLetter2PathProgramLetter.put((LETTER) current.getLabel(), (LETTER) current);
			}
			final List<LETTER> rtr = new ArrayList<>(word.length());
			for (final LETTER letter : word.asList()) {
				final LETTER ppLetter = wordLetter2PathProgramLetter.get(letter);
				assert ppLetter != null : "Path program construction broken";
				rtr.add(ppLetter);
			}
			assert rtr.size() == word.length();
			return rtr;
		}

		private boolean isInductive(final List<LETTER> trace, final List<AbsIntPredicate<STATE>> interpolants,
				final IHoareTripleChecker htc) {
			mLogger.debug("Checking inductivity of AbsInt predicates");
			if (trace.isEmpty()) {
				return true;
			}
			assert trace.size() == interpolants.size() + 1 : "trace size does not match interpolants size";

			final List<AbsIntPredicate<STATE>> completeInterpolants = new ArrayList<>();
			completeInterpolants.add(mTruePredicate);
			completeInterpolants.addAll(interpolants);
			completeInterpolants.add(mFalsePredicate);

			final Iterator<LETTER> traceIter = trace.iterator();
			final Iterator<AbsIntPredicate<STATE>> interpolantsIter = completeInterpolants.iterator();

			AbsIntPredicate<STATE> pre = null;
			AbsIntPredicate<STATE> post = interpolantsIter.next();
			final Deque<AbsIntPredicate<STATE>> preHierStates = new ArrayDeque<>();
			while (interpolantsIter.hasNext()) {
				pre = post;
				post = interpolantsIter.next();
				final LETTER trans = traceIter.next();
				assert trans != null;

				final Validity result;
				final IPredicate preHier;
				if (trans instanceof IInternalAction) {
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(String.format("Checking {%s} %s {%s}", pre, trans, post));
					}
					preHier = null;
					result = htc.checkInternal(pre, (IInternalAction) trans, post);
				} else if (trans instanceof ICallAction) {
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(String.format("Checking {%s} %s {%s}", pre, trans, post));
					}
					preHierStates.addFirst(pre);
					preHier = null;
					result = htc.checkCall(pre, (ICallAction) trans, post);
				} else if (trans instanceof IReturnAction) {
					preHier = preHierStates.removeFirst();
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(String.format("Checking {%s} {%s} %s {%s}", pre, preHier, trans, post));
					}
					result = htc.checkReturn(pre, preHier, (IReturnAction) trans, post);
				} else {
					throw new UnsupportedOperationException("Unknown transition type " + trans.getClass());
				}

				if (result != Validity.VALID) {
					// the absint htc must solve all queries from those interpolants, therefore the result must be VALID
					mLogger.fatal("Inductivity check failed! Result is " + result + " for "
							+ trans.getClass().getSimpleName() + " transition");
					mLogger.fatal("Prestate:       " + pre.toString());
					if (preHier != null) {
						mLogger.fatal("HierState:      " + preHier.toString());
					}
					if (trans instanceof IReturnAction) {
						final IReturnAction rtrAction = (IReturnAction) trans;
						mLogger.fatal("Transition(R) : " + rtrAction.getAssignmentOfReturn());
						mLogger.fatal("Transition(LV): " + rtrAction.getLocalVarsAssignmentOfCall());
					} else {
						mLogger.fatal("Transition    : " + trans.getTransformula());
					}
					mLogger.fatal("Poststate:      " + post.toString());
					return false;
				}
			}
			return true;
		}

		private List<AbsIntPredicate<STATE>> generateAbsIntPredicates(final List<LETTER> cexTrace) {
			final List<AbsIntPredicate<STATE>> rtr = new ArrayList<>();
			final Deque<LETTER> callstack = new ArrayDeque<>();
			final Script script = mCsToolkit.getManagedScript().getScript();
			Set<STATE> previousStates = Collections.emptySet();
			for (final LETTER symbol : cexTrace) {
				if (symbol instanceof ICallAction) {
					callstack.addFirst(symbol);
				} else if (symbol instanceof IReturnAction) {
					callstack.removeFirst();
				}
				final Set<STATE> postStates = mResult.getPostStates(callstack, symbol, previousStates);
				final AbsIntPredicate<STATE> next = getNonUnifiedPredicateFromStates(postStates, script);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(String.format("[%s] %s %s", symbol.hashCode(), symbol, next));
				}
				previousStates = postStates;
				rtr.add(next);
			}
			final AbsIntPredicate<STATE> lastPred = rtr.remove(rtr.size() - 1);
			assert lastPred.getFormula().toString().equals("false");
			return rtr;
		}

		@SuppressWarnings("unchecked")
		private AbsIntPredicate<STATE> getPredicateFromStates(final Set<STATE> postStates, final Script script) {
			if (postStates.isEmpty()) {
				return mFalsePredicate;
			}

			final DisjunctiveAbstractState<STATE> disjunctiveState =
					DisjunctiveAbstractState.createDisjunction(postStates);
			final IPredicate unUnifiedPredicate =
					mPredicateUnifierSmt.getPredicateFactory().newPredicate(disjunctiveState.getTerm(script));
			final IPredicate disjunction = mPredicateUnifierAbsInt
					.getOrConstructPredicate(new AbsIntPredicate<>(unUnifiedPredicate, disjunctiveState));
			if (disjunction.equals(mFalsePredicate)) {
				return mFalsePredicate;
			}
			if (disjunction.equals(mTruePredicate)) {
				return mTruePredicate;
			}
			assert disjunction instanceof AbsIntPredicate<?>;
			return (AbsIntPredicate<STATE>) disjunction;
		}

		@SuppressWarnings("unchecked")
		private AbsIntPredicate<STATE> getNonUnifiedPredicateFromStates(final Set<STATE> postStates,
				final Script script) {
			if (postStates.isEmpty()) {
				return mFalsePredicate;
			}
			final BasicPredicateFactory predFac = mPredicateUnifierAbsInt.getPredicateFactory();
			final DisjunctiveAbstractState<STATE> disjunctiveState =
					DisjunctiveAbstractState.createDisjunction(postStates).compact();
			final IPredicate disjunction = predFac.newPredicate(disjunctiveState.getTerm(script));
			return new AbsIntPredicate<>(disjunction, (STATE) disjunctiveState);
		}
	}

	public static final class AbsIntInterpolantGenerator<L extends IAction> extends AbsIntBaseInterpolantGenerator<L> {

		private final IPredicate[] mInterpolants;
		private final CachingHoareTripleChecker mHtc;

		private AbsIntInterpolantGenerator(final IPredicateUnifier predicateUnifier, final Word<L> cex,
				final IPredicate[] sequence, final CachingHoareTripleChecker htc, final AbsIntPredicate<?> preCond,
				final AbsIntPredicate<?> postCond) {
			super(predicateUnifier, cex, preCond, postCond, new InterpolantComputationStatus());
			mInterpolants = Objects.requireNonNull(sequence);
			mHtc = Objects.requireNonNull(htc);
		}

		@Override
		public CachingHoareTripleChecker getHoareTripleChecker() {
			return mHtc;
		}

		@Override
		public Map<Integer, IPredicate> getPendingContexts() {
			return null;
		}

		@Override
		public IPredicate[] getInterpolants() {
			return mInterpolants;
		}

		@Override
		public boolean isPerfectSequence() {
			// if we have a sequence, its always perfect
			return true;
		}

		@Override
		public LBool isCorrect() {
			return LBool.UNSAT;
		}

		@Override
		public boolean providesRcfgProgramExecution() {
			return false;
		}

		@Override
		public IProgramExecution<L, Term> getRcfgProgramExecution() {
			throw new UnsupportedOperationException();
		}

		@Override
		public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean wasTracecheckFinishedNormally() {
			return true;
		}

		@Override
		public IStatisticsDataProvider getStatistics() {
			throw new UnsupportedOperationException();
		}

	}

	private static final class AbsIntFailedInterpolantGenerator<L extends IAction>
			extends AbsIntBaseInterpolantGenerator<L> {

		private final TraceCheckReasonUnknown mReason;

		private AbsIntFailedInterpolantGenerator(final IPredicateUnifier predicateUnifier, final Word<L> cex,
				final ItpErrorStatus status, final Exception ex) {
			super(predicateUnifier, cex, null, null, new InterpolantComputationStatus(status, ex));
			mReason = new TraceCheckReasonUnknown(Reason.SOLVER_RESPONSE_OTHER, ex,
					ExceptionHandlingCategory.KNOWN_IGNORE);
		}

		@Override
		public Map<Integer, IPredicate> getPendingContexts() {
			throw new UnsupportedOperationException();
		}

		@Override
		public IPredicate[] getInterpolants() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isPerfectSequence() {
			// if we fail there is no sequence
			return false;
		}

		@Override
		public CachingHoareTripleChecker getHoareTripleChecker() {
			throw new UnsupportedOperationException();
		}

		@Override
		public LBool isCorrect() {
			return LBool.UNKNOWN;
		}

		@Override
		public boolean providesRcfgProgramExecution() {
			return false;
		}

		@Override
		public IProgramExecution<L, Term> getRcfgProgramExecution() {
			throw new UnsupportedOperationException();
		}

		@Override
		public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
			return mReason;
		}

		@Override
		public boolean wasTracecheckFinishedNormally() {
			return true;
		}

		@Override
		public IStatisticsDataProvider getStatistics() {
			throw new UnsupportedOperationException();
		}
	}

}
