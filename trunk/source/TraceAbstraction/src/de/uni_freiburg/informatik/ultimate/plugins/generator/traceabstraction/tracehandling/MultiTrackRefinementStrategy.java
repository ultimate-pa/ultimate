/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder.InitialAndAcceptingStateMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * {@link IRefinementStrategy} that uses different {@link Track}s.
 * <p>
 * The class uses a {@link StraightLineInterpolantAutomatonBuilder} for constructing the interpolant automaton.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public abstract class MultiTrackRefinementStrategy<LETTER extends IIcfgTransition<?>>
		extends BaseRefinementStrategy<LETTER> {
	/**
	 * Possible tracks.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum Track {
		/**
		 * SMTInterpol with tree interpolation.
		 */
		SMTINTERPOL_TREE_INTERPOLANTS,
		/**
		 * SMTInterpol with forward predicates.
		 */
		SMTINTERPOL_FP,
		/**
		 * SMTInterpol with tree interpolation and disabled array interpolation (it will crash).
		 */
		SMTINTERPOL_TREE_INTERPOLANTS_NO_ARRAY,
		/**
		 * Z3 with forward and backward predicates.
		 */
		Z3_FPBP,
		/**
		 * Z3 with forward predicates.
		 */
		Z3_FP,
		/**
		 * Z3 with Craig interpolation.
		 */
		Z3_NESTED_INTERPOLANTS,
		/**
		 * CVC4 with forward and backward predicates.
		 */
		CVC4_FPBP,
		/**
		 * CVC4 with forward predicates.
		 */
		CVC4_FP,
		/**
		 * MathSAT with forward and backward predicates.
		 */
		MATHSAT_FPBP,
		/**
		 * MathSAT with forward predicates.
		 */
		MATHSAT_FP,

		/**
		 * PDR with hard-coded solver
		 */
		PDR
	}

	private static final String UNKNOWN_MODE = "Unknown mode: ";

	protected final IRun<LETTER, IPredicate, ?> mCounterexample;
	private final IPredicate mPrecondition;

	private final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;
	private final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	protected final CfgSmtToolkit mCsToolkit;
	private final AssertionOrderModulation<LETTER> mAssertionOrderModulation;
	private final IAutomaton<LETTER, IPredicate> mAbstraction;
	private final PredicateFactory mPredicateFactory;
	private final IPredicateUnifier mPredicateUnifier;

	// TODO Christian 2016-11-11: Matthias wants to get rid of this
	private final TAPreferences mTaPrefsForInterpolantConsolidation;

	private final Iterator<Track> mInterpolationTechniques;

	private TraceCheckConstructor<LETTER> mTcConstructor;
	private TraceCheckConstructor<LETTER> mPrevTcConstructor;
	private Track mNextTechnique;

	// store if the trace has already been shown to be infeasible in a previous attempt
	private boolean mHasShownInfeasibilityBefore;

	private ITraceCheck mTraceCheck;
	private IInterpolantGenerator<LETTER> mInterpolantGenerator;
	private IInterpolantAutomatonBuilder<LETTER, IPredicate> mInterpolantAutomatonBuilder;
	protected final TaskIdentifier mTaskIdentifier;
	private final RefinementEngineStatisticsGenerator mRefinementEngineStatisticsGenerator;

	/**
	 * @param prefs
	 *            Preferences. pending contexts
	 * @param services
	 *            Ultimate services
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param counterexample
	 *            counterexample trace
	 * @param logger
	 *            logger
	 * @param cfgSmtToolkit
	 * @param abstraction
	 *            abstraction
	 * @param taPrefsForInterpolantConsolidation
	 *            temporary argument, should be removed
	 * @param assertionOrderModulation
	 *            assertion order modulation
	 * @param precondition
	 * @param cegarLoopBenchmarks
	 *            benchmark
	 */
	@SuppressWarnings("squid:S1699")
	protected MultiTrackRefinementStrategy(final ILogger logger, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier,
			final AssertionOrderModulation<LETTER> assertionOrderModulation,
			final IRun<LETTER, IPredicate, ?> counterexample, final IPredicate precondition,
			final IAutomaton<LETTER, IPredicate> abstraction, final TAPreferences taPrefsForInterpolantConsolidation,
			final TaskIdentifier taskIdentifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		super(logger, emptyStackFactory);
		mServices = services;
		mLogger = logger;
		mPrefs = prefs;
		mCsToolkit = cfgSmtToolkit;
		mAssertionOrderModulation = assertionOrderModulation;
		mCounterexample = counterexample;
		mPrecondition = precondition;
		mAbstraction = abstraction;
		mPredicateFactory = predicateFactory;
		mPredicateUnifier = predicateUnifier;
		mTaskIdentifier = taskIdentifier;
		mTaPrefsForInterpolantConsolidation = taPrefsForInterpolantConsolidation;
		mRefinementEngineStatisticsGenerator = new RefinementEngineStatisticsGenerator();

		mInterpolationTechniques = initializeInterpolationTechniquesList();
		nextTraceCheck();
	}

	@Override
	public boolean hasNextTraceCheck() {
		return mInterpolationTechniques.hasNext();
	}

	@Override
	public void nextTraceCheck() {
		if (mNextTechnique != null) {
			throw new UnsupportedOperationException("Try the existing combination before advancing.");
		}
		mNextTechnique = mInterpolationTechniques.next();

		// reset trace checker, interpolant generator, and constructor
		mTraceCheck = null;
		mInterpolantGenerator = null;
		mPrevTcConstructor = mTcConstructor;
		mTcConstructor = null;

		mLogger.info("Switched to mode " + mNextTechnique);
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
	public boolean hasNextInterpolantGenerator(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) {
		if (!hasNextInterpolantGeneratorAvailable()) {
			return false;
		}

		// stop after finding a perfect interpolant sequence; subclasses may have more sophisticated conditions
		if (!perfectIpps.isEmpty()) {
			return false;
		}
		return imperfectIpps.size() < getInterpolantAcceptanceThreshold();
	}

	/**
	 * Do not search for more interpolants if you already found a perfect interpolant sequence OR this number of
	 * imperfect interpolant sequences.
	 *
	 * @return the number of imperfect sequences after which this strategy is satisfied.
	 */
	protected abstract int getInterpolantAcceptanceThreshold();

	protected boolean hasNextInterpolantGeneratorAvailable() {
		return mInterpolationTechniques.hasNext();
	}

	@Override
	public void nextInterpolantGenerator() {
		nextTraceCheck();
	}

	@Override
	public IInterpolantGenerator<LETTER> getInterpolantGenerator() {
		mHasShownInfeasibilityBefore = true;
		if (mInterpolantGenerator == null) {
			mInterpolantGenerator = RefinementStrategyUtils.constructInterpolantGenerator(mServices, mLogger, mPrefs,
					mTaPrefsForInterpolantConsolidation, getTraceCheck(), mPredicateFactory, mPredicateUnifier,
					mCounterexample, mPrecondition, mRefinementEngineStatisticsGenerator);
		}
		return mInterpolantGenerator;
	}

	@Override
	public IInterpolantAutomatonBuilder<LETTER, IPredicate> getInterpolantAutomatonBuilder(
			final List<TracePredicates> perfectIpps, final List<TracePredicates> imperfectIpps) {
		// current policy: use all interpolant sequences
		final List<TracePredicates> allIpps = DataStructureUtils.concat(perfectIpps, imperfectIpps);

		if (mInterpolantAutomatonBuilder == null) {
			mInterpolantAutomatonBuilder = new StraightLineInterpolantAutomatonBuilder<>(mServices,
					mCounterexample.getWord(), NestedWordAutomataUtils.getVpAlphabet(mAbstraction), allIpps,
					mEmptyStackFactory, InitialAndAcceptingStateMode.ONLY_FIRST_INITIAL_ONLY_FALSE_ACCEPTING);
		}
		return mInterpolantAutomatonBuilder;
	}

	/**
	 * @return iterator of different combinations.
	 */
	protected abstract Iterator<Track> initializeInterpolationTechniquesList();

	private TraceCheckConstructor<LETTER> constructTraceCheckConstructor() {
		final InterpolationTechnique interpolationTechnique = getInterpolationTechnique(mNextTechnique);

		final boolean useTimeout = mHasShownInfeasibilityBefore;
		final ManagedScript managedScript = constructManagedScript(mServices, mPrefs, mNextTechnique, useTimeout);

		final AssertCodeBlockOrder assertionOrder =
				mAssertionOrderModulation.get(mCounterexample, interpolationTechnique);

		mNextTechnique = null;

		TraceCheckConstructor<LETTER> result;
		if (mPrevTcConstructor == null) {
			result = new TraceCheckConstructor<>(mPrefs, managedScript, mServices, mPredicateFactory, mPredicateUnifier,
					mCounterexample, mPrecondition, assertionOrder, interpolationTechnique, mTaskIdentifier);
		} else {
			result = new TraceCheckConstructor<>(mPrevTcConstructor, managedScript, assertionOrder,
					interpolationTechnique);
		}
		return result;
	}

	private static InterpolationTechnique getInterpolationTechnique(final Track mode) {
		final InterpolationTechnique interpolationTechnique;
		switch (mode) {
		case SMTINTERPOL_TREE_INTERPOLANTS:
		case SMTINTERPOL_TREE_INTERPOLANTS_NO_ARRAY:
			interpolationTechnique = InterpolationTechnique.Craig_TreeInterpolation;
			break;
		case Z3_NESTED_INTERPOLANTS:
			interpolationTechnique = InterpolationTechnique.Craig_NestedInterpolation;
			break;
		case Z3_FPBP:
		case CVC4_FPBP:
		case MATHSAT_FPBP:
			interpolationTechnique = InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect;
			break;
		case Z3_FP:
		case SMTINTERPOL_FP:
		case CVC4_FP:
		case MATHSAT_FP:
			interpolationTechnique = InterpolationTechnique.ForwardPredicates;
			break;
		case PDR:
			interpolationTechnique = InterpolationTechnique.PDR;
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
		return interpolationTechnique;
	}

	@SuppressWarnings("squid:S1151")
	private ManagedScript constructManagedScript(final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final Track mode, final boolean useTimeout) {
		final boolean dumpSmtScriptToFile = prefs.getDumpSmtScriptToFile();
		final String pathOfDumpedScript = prefs.getPathOfDumpedScript();
		final String baseNameOfDumpedScript = mTaskIdentifier.toString();
		final SolverSettings solverSettings;
		final SolverMode solverMode;
		final String logicForExternalSolver;
		final String command;
		switch (mode) {
		case SMTINTERPOL_TREE_INTERPOLANTS:
		case SMTINTERPOL_FP:
		case SMTINTERPOL_TREE_INTERPOLANTS_NO_ARRAY:
			final long timeout =
					useTimeout ? SolverBuilder.TIMEOUT_SMTINTERPOL : SolverBuilder.TIMEOUT_NONE_SMTINTERPOL;
			solverSettings = new SolverSettings(false, false, null, timeout, null, dumpSmtScriptToFile,
					pathOfDumpedScript, baseNameOfDumpedScript);
			solverMode = mode == Track.SMTINTERPOL_TREE_INTERPOLANTS_NO_ARRAY
					? SolverMode.Internal_SMTInterpol_NoArrayInterpol
					: SolverMode.Internal_SMTInterpol;
			logicForExternalSolver = null;
			break;
		case Z3_NESTED_INTERPOLANTS:
			throw new AssertionError("The mode " + Track.Z3_NESTED_INTERPOLANTS + "is currently unsupported.");
			/*
			 * command = useTimeout ? COMMAND_Z3_TIMEOUT : COMMAND_Z3_NO_TIMEOUT; // TODO: Add external interpolator
			 * String externalInterpolator = null; solverSettings = new Settings(false, true, command, 0,
			 * externalInterpolator, dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript); solverMode =
			 * SolverMode.External_Z3InterpolationMode; logicForExternalSolver = LOGIC_Z3; break;
			 */
		case Z3_FPBP:
		case Z3_FP:
			command = useTimeout ? SolverBuilder.COMMAND_Z3_TIMEOUT : SolverBuilder.COMMAND_Z3_NO_TIMEOUT;
			solverSettings = new SolverSettings(false, true, command, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
			logicForExternalSolver = SolverBuilder.LOGIC_Z3;
			break;
		case CVC4_FPBP:
		case CVC4_FP:
			command = useTimeout ? SolverBuilder.COMMAND_CVC4_TIMEOUT : SolverBuilder.COMMAND_CVC4_NO_TIMEOUT;
			solverSettings = new SolverSettings(false, true, command, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
			logicForExternalSolver = getCvc4Logic();
			break;
		case MATHSAT_FPBP:
		case MATHSAT_FP:
			command = SolverBuilder.COMMAND_MATHSAT;
			solverSettings = new SolverSettings(false, true, command, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
			logicForExternalSolver = SolverBuilder.LOGIC_MATHSAT;
			break;
		case PDR:
			command = useTimeout ? SolverBuilder.COMMAND_Z3_TIMEOUT : SolverBuilder.COMMAND_Z3_NO_TIMEOUT;
			solverSettings = new SolverSettings(false, true, command, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsMode;
			logicForExternalSolver = SolverBuilder.LOGIC_Z3;
			break;
		default:
			throw new IllegalArgumentException(
					"Managed script construction not supported for interpolation technique: " + mode);
		}
		final Script solver = SolverBuilder.buildAndInitializeSolver(services, prefs.getToolchainStorage(), solverMode,
				solverSettings, false, false, logicForExternalSolver, "TraceCheck_Iteration" + mTaskIdentifier);
		final ManagedScript result = new ManagedScript(services, solver);
		prefs.getIcfgContainer().getCfgSmtToolkit().getSmtSymbols().transferSymbols(solver);
		return result;
	}

	/**
	 * @return Logic string used for {@code CVC4}.
	 */
	protected abstract String getCvc4Logic();

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public RefinementStrategyExceptionBlacklist getExceptionBlacklist() {
		return mPrefs.getExceptionBlacklist();
	}

	@Override
	public RefinementEngineStatisticsGenerator getRefinementEngineStatistics() {
		return mRefinementEngineStatisticsGenerator;
	}

}
