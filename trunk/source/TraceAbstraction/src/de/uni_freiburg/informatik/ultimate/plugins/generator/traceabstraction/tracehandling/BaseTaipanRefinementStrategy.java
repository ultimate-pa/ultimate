/*
 * Copyright (C) 2016-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder.InitialAndAcceptingStateMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * {@link IRefinementStrategy} that is used by Taipan. It first tries an {@link InterpolatingTraceCheck} using
 * {@link SMTInterpol} with {@link InterpolationTechnique#Craig_TreeInterpolation}.<br>
 * If successful and the interpolant sequence is perfect, those interpolants are used.<br>
 * If not successful, it tries {@link TraceCheck} {@code Z3} and, if again not successful, {@code CVC4}.<br>
 * If none of those is successful, the strategy gives up.<br>
 * Otherwise, if the trace is infeasible, the strategy uses an {@link CegarAbsIntRunner} to construct interpolants.<br>
 * If not successful, the strategy again tries {@code Z3} and {@code CVC4}, but this time using interpolation
 * {@link InterpolationTechnique#FPandBP}.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public abstract class BaseTaipanRefinementStrategy<LETTER extends IIcfgTransition<?>>
		extends BaseRefinementStrategy<LETTER> {
	protected static final String UNKNOWN_MODE = "Unknown mode: ";

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	private final PredicateFactory mPredicateFactory;
	protected final IPredicateUnifier mPredicateUnifierSmt;
	protected final CegarAbsIntRunner<LETTER> mAbsIntRunner;
	private final AssertionOrderModulation<LETTER> mAssertionOrderModulation;
	protected final IRun<LETTER, IPredicate, ?> mCounterexample;
	private final IPredicate mPrecondition;
	protected final IAutomaton<LETTER, IPredicate> mAbstraction;

	private Mode mCurrentMode;

	// store if the trace has already been shown to be infeasible in a previous attempt
	private boolean mHasShownInfeasibilityBefore;

	private TraceCheckConstructor<LETTER> mTcConstructor;
	private TraceCheckConstructor<LETTER> mPrevTcConstructor;

	private ITraceCheck mTraceCheck;
	private IInterpolantGenerator<LETTER> mInterpolantGenerator;
	private IInterpolantAutomatonBuilder<LETTER, IPredicate> mInterpolantAutomatonBuilder;
	private final TaskIdentifier mTaskIdentifier;
	private final RefinementEngineStatisticsGenerator mRefinementEngineStatisticsGenerator;

	/**
	 * @param logger
	 *            Logger.
	 * @param services
	 *            Ultimate services
	 * @param prefs
	 *            preferences
	 * @param cfgSmtToolkit
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param absIntRunner
	 *            abstract interpretation runner
	 * @param assertionOrderModulation
	 *            assertion order modulation
	 * @param counterexample
	 *            counterexample
	 * @param abstraction
	 *            abstraction
	 * @param cegarLoopBenchmark
	 *            benchmark
	 */
	public BaseTaipanRefinementStrategy(final ILogger logger, final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier,
			final CegarAbsIntRunner<LETTER> absIntRunner,
			final AssertionOrderModulation<LETTER> assertionOrderModulation,
			final IRun<LETTER, IPredicate, ?> counterexample, final IPredicate precondition,
			final IAutomaton<LETTER, IPredicate> abstraction, final TaskIdentifier taskIdentifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		super(logger, emptyStackFactory);
		mServices = services;
		mLogger = logger;
		mPrefs = prefs;
		mPredicateFactory = predicateFactory;
		mPredicateUnifierSmt = predicateUnifier;
		mAbsIntRunner = absIntRunner;
		mAssertionOrderModulation = assertionOrderModulation;
		mCounterexample = counterexample;
		mPrecondition = precondition;
		mAbstraction = abstraction;
		mTaskIdentifier = taskIdentifier;
		mRefinementEngineStatisticsGenerator = new RefinementEngineStatisticsGenerator();

		mCurrentMode = getInitialMode();
	}

	protected abstract Mode getInitialMode();

	@Override
	public abstract boolean hasNextTraceCheck();

	@Override
	public void nextTraceCheck() {
		final Mode nextMode = getNextTraceCheckMode();
		mCurrentMode = nextMode;

		// reset trace checker, interpolant generator, and constructor
		mInterpolantGenerator = null;
		resetTraceCheck();

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Switched to traceCheck mode " + mCurrentMode);
		}
	}

	protected abstract Mode getNextTraceCheckMode();

	@Override
	public boolean hasNextInterpolantGenerator(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) {
		// current policy: stop after finding one perfect interpolant sequence
		return perfectIpps.isEmpty() && hasNextInterpolantGeneratorAvailable();
	}

	protected abstract boolean hasNextInterpolantGeneratorAvailable();

	@Override
	public void nextInterpolantGenerator() {
		final Mode nextMode = getNextInterpolantGenerator();
		mCurrentMode = nextMode;

		mInterpolantGenerator = null;

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Switched to InterpolantGenerator mode " + mCurrentMode);
		}
	}

	protected void resetTraceCheck() {
		mTraceCheck = null;
		mPrevTcConstructor = mTcConstructor;
		mTcConstructor = null;
	}

	protected abstract Mode getNextInterpolantGenerator();

	protected Mode getCurrentMode() {
		return mCurrentMode;
	}

	@Override
	public ITraceCheck getTraceCheck() {
		if (mTraceCheck == null) {
			if (mTcConstructor == null) {
				mTcConstructor = constructTraceCheckConstructor();
			}
			mTraceCheck = mTcConstructor.get();
			mRefinementEngineStatisticsGenerator.addTraceCheckStatistics(mTraceCheck);
		}
		return mTraceCheck;
	}

	@Override
	public IInterpolantGenerator<LETTER> getInterpolantGenerator() {
		mHasShownInfeasibilityBefore = true;
		if (mInterpolantGenerator == null) {
			mInterpolantGenerator = constructInterpolantGenerator(mCurrentMode);
		}
		return mInterpolantGenerator;
	}

	@Override
	public IInterpolantAutomatonBuilder<LETTER, IPredicate> getInterpolantAutomatonBuilder(
			final List<TracePredicates> perfectIpps, final List<TracePredicates> imperfectIpps) {
		if (mInterpolantAutomatonBuilder == null) {
			mInterpolantAutomatonBuilder =
					constructInterpolantAutomatonBuilder(perfectIpps, imperfectIpps, mCurrentMode, mEmptyStackFactory);
		}
		return mInterpolantAutomatonBuilder;
	}

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> constructInterpolantAutomatonBuilder(
			final List<TracePredicates> perfectIpps, final List<TracePredicates> imperfectIpps, final Mode mode,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		switch (mode) {
		case ABSTRACT_INTERPRETATION:
		case SMTINTERPOL:
		case Z3_IG:
		case CVC4_IG:
			if (perfectIpps.isEmpty()) {
				// if we have only imperfect interpolants, we take the first two
				mLogger.info("Using the first two imperfect interpolant sequences");
				return new StraightLineInterpolantAutomatonBuilder<>(mServices, mCounterexample.getWord(),
						NestedWordAutomataUtils.getVpAlphabet(mAbstraction),
						imperfectIpps.stream().limit(2).collect(Collectors.toList()), emptyStackFactory,
						InitialAndAcceptingStateMode.ONLY_FIRST_INITIAL_ONLY_FALSE_ACCEPTING);
			}
			// if we have some perfect, we take one of those
			mLogger.info("Using the first perfect interpolant sequence");
			final List<TracePredicates> ippSequence = perfectIpps.stream().limit(1).collect(Collectors.toList());
			assert mode != Mode.ABSTRACT_INTERPRETATION || ippSequence.get(0).getPredicates().stream()
					.allMatch(a -> a instanceof AbsIntPredicate<?>) : "AbsInt did not yield AbsIntPredicates";
			return new StraightLineInterpolantAutomatonBuilder<>(mServices, mCounterexample.getWord(),
					NestedWordAutomataUtils.getVpAlphabet(mAbstraction), ippSequence, emptyStackFactory,
					InitialAndAcceptingStateMode.ONLY_FIRST_INITIAL_ONLY_FALSE_ACCEPTING);
		case Z3_NO_IG:
		case CVC4_NO_IG:
			throw new AssertionError("The mode " + mode + " should be unreachable here.");
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
	}

	private TraceCheckConstructor<LETTER> constructTraceCheckConstructor() {
		final InterpolationTechnique interpolationTechnique = getInterpolationTechnique(mCurrentMode);
		final boolean useTimeout = mHasShownInfeasibilityBefore;

		final Mode scriptMode;
		if (CoreUtil.OS_IS_WINDOWS) {
			scriptMode = getModeForWindowsUsers();
		} else {
			scriptMode = mCurrentMode;
		}

		final ManagedScript managedScript =
				constructManagedScript(mServices, mPrefs, scriptMode, useTimeout, mTaskIdentifier);

		final AssertCodeBlockOrder assertionOrder =
				mAssertionOrderModulation.get(mCounterexample, interpolationTechnique);

		mLogger.info("Using traceCheck mode " + mCurrentMode + " with AssertCodeBlockOrder " + assertionOrder + " (IT: "
				+ interpolationTechnique + ")");
		TraceCheckConstructor<LETTER> result;
		if (mPrevTcConstructor == null) {
			result = new TraceCheckConstructor<>(mPrefs, managedScript, mServices, mPredicateFactory,
					mPredicateUnifierSmt, mCounterexample, mPrecondition, assertionOrder, interpolationTechnique,
					mTaskIdentifier);
		} else {
			result = new TraceCheckConstructor<>(mPrevTcConstructor, managedScript, assertionOrder,
					interpolationTechnique);
		}
		return result;
	}

	/**
	 * Because we rely on the "golden copy" of CVC4 and we only have this for Linux, windows users are screwed during
	 * debugging. To enable at least some debugging, we hack the mode if someone is a poor windows user.
	 */
	private Mode getModeForWindowsUsers() {
		final Mode modeHack;
		if (mCurrentMode == Mode.CVC4_IG || mCurrentMode == Mode.CVC4_NO_IG) {
			modeHack = getWindowsCvcReplacementMode(mCurrentMode);
		} else {
			modeHack = mCurrentMode;
		}
		if (modeHack != mCurrentMode) {
			mLogger.warn("Poor windows users use " + modeHack + " instead of " + mCurrentMode);
		}
		return modeHack;
	}

	protected abstract Mode getWindowsCvcReplacementMode(Mode cvcMode);

	protected abstract InterpolationTechnique getInterpolationTechnique(final Mode mode);

	@SuppressWarnings("squid:S1151")
	private ManagedScript constructManagedScript(final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final Mode mode, final boolean useTimeout,
			final TaskIdentifier taskIdentifier) {
		final boolean dumpSmtScriptToFile = prefs.getDumpSmtScriptToFile();
		final String pathOfDumpedScript = prefs.getPathOfDumpedScript();
		final String baseNameOfDumpedScript = taskIdentifier.toString();
		final SolverSettings solverSettings;
		final SolverMode solverMode;
		final String logicForExternalSolver;
		final String command;
		switch (mode) {
		case SMTINTERPOL:
		case ABSTRACT_INTERPRETATION:
			final long timeout =
					useTimeout ? SolverBuilder.TIMEOUT_SMTINTERPOL : SolverBuilder.TIMEOUT_NONE_SMTINTERPOL;
			solverSettings = new SolverSettings(false, false, null, timeout, null, dumpSmtScriptToFile,
					pathOfDumpedScript, baseNameOfDumpedScript);
			solverMode = SolverMode.Internal_SMTInterpol;
			logicForExternalSolver = null;
			break;
		case Z3_IG:
		case Z3_NO_IG:
			command = useTimeout ? SolverBuilder.COMMAND_Z3_TIMEOUT : SolverBuilder.COMMAND_Z3_NO_TIMEOUT;
			solverSettings = new SolverSettings(false, true, command, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
			logicForExternalSolver = SolverBuilder.LOGIC_Z3;
			break;
		case CVC4_IG:
		case CVC4_NO_IG:
			command = useTimeout ? SolverBuilder.COMMAND_CVC4_TIMEOUT : SolverBuilder.COMMAND_CVC4_NO_TIMEOUT;
			solverSettings = new SolverSettings(false, true, command, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
			logicForExternalSolver = SolverBuilder.LOGIC_CVC4_DEFAULT;
			break;
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
		final Script solver = SolverBuilder.buildAndInitializeSolver(services, prefs.getToolchainStorage(), solverMode,
				solverSettings, false, false, logicForExternalSolver, "TraceCheck_Iteration" + taskIdentifier);
		final ManagedScript result = new ManagedScript(services, solver);
		prefs.getCfgSmtToolkit().getSmtSymbols().transferSymbols(solver);
		return result;
	}

	private IInterpolantGenerator<LETTER> constructInterpolantGenerator(final Mode mode) {
		switch (mode) {
		case SMTINTERPOL:
		case CVC4_IG:
			return castTraceCheck();
		case Z3_IG:
			return castTraceCheck();
		case Z3_NO_IG:
		case CVC4_NO_IG:
		case ABSTRACT_INTERPRETATION:
			mCurrentMode = Mode.ABSTRACT_INTERPRETATION;
			mAbsIntRunner.generateFixpoints(mCounterexample,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, mPredicateUnifierSmt);
			return mAbsIntRunner.getInterpolantGenerator();
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
	}

	private IInterpolantGenerator<LETTER> castTraceCheck() {
		final ITraceCheck traceCheck = getTraceCheck();
		assert traceCheck != null && traceCheck instanceof IInterpolantGenerator;
		return (IInterpolantGenerator<LETTER>) traceCheck;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		if (mCurrentMode == Mode.ABSTRACT_INTERPRETATION) {
			if (getInterpolantGenerator().getInterpolantComputationStatus().wasComputationSuccesful()) {
				return getInterpolantGenerator().getPredicateUnifier();
			}
		}
		return mPredicateUnifierSmt;
	}

	@Override
	public RefinementStrategyExceptionBlacklist getExceptionBlacklist() {
		return RefinementStrategyExceptionBlacklist.UNKNOWN;
	}

	@Override
	public RefinementEngineStatisticsGenerator getRefinementEngineStatistics() {
		return mRefinementEngineStatisticsGenerator;
	}

	/**
	 * Current mode in this strategy.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	protected enum Mode {
		/**
		 * SMTInterpol with tree interpolation.
		 */
		SMTINTERPOL,
		/**
		 * Z3 without interpolant generation.
		 */
		Z3_NO_IG,
		/**
		 * CVC4 without interpolant generation.
		 */
		CVC4_NO_IG,
		/**
		 * Abstract interpretation.
		 */
		ABSTRACT_INTERPRETATION,
		/**
		 * Z3 with interpolant generation.
		 */
		Z3_IG,
		/**
		 * CVC4 with interpolant generation.
		 */
		CVC4_IG,
	}
}
