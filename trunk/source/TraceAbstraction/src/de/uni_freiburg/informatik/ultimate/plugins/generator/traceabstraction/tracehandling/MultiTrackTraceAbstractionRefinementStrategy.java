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
import java.util.Objects;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.MultiTrackInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

/**
 * {@link IRefinementStrategy} that first tries an {@link InterpolatingTraceChecker} using
 * {@link InterpolationTechnique#Craig_TreeInterpolation} and then {@link InterpolationTechnique#FPandBP}.
 * <p>
 * The class uses a {@link MultiTrackInterpolantAutomatonBuilder} for constructing the interpolant automaton.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public abstract class MultiTrackTraceAbstractionRefinementStrategy<LETTER extends IIcfgTransition<?>>
		implements IRefinementStrategy<LETTER> {
	/**
	 * Possible tracks.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	protected enum Track {
		/**
		 * SMTInterpol with tree interpolation.
		 */
		SMTINTERPOL_TREE_INTERPOLANTS, SMTINTERPOL_FP,
		/**
		 * Z3 with forward and backward predicates.
		 */
		Z3_FPBP, Z3_FP,
		/**
		 * Z3 with Craig interpolation.
		 */
		Z3_NESTED_INTERPOLANTS,
		/**
		 * CVC4 with forward and backward predicates.
		 */
		CVC4_FPBP, CVC4_FP,
		/**
		 * MathSAT with forward and backward predicates.
		 */
		MATHSAT_FPBP, MATHSAT_FP,
	}

	private static final int INTERPOLANT_ACCEPTANCE_THRESHOLD = 2;
	private static final String UNKNOWN_MODE = "Unknown mode: ";

	protected final IRun<LETTER, IPredicate, ?> mCounterexample;

	protected final StrategyContext<LETTER> mContext;
	private final IAutomaton<LETTER, IPredicate> mAbstraction;
	private final PredicateUnifier mPredicateUnifier;

	private final Iterator<Track> mInterpolationTechniques;

	private TraceCheckerConstructor<LETTER> mTcConstructor;
	private TraceCheckerConstructor<LETTER> mPrevTcConstructor;
	private Track mNextTechnique;

	// store if the trace has already been shown to be infeasible in a previous attempt
	private boolean mHasShownInfeasibilityBefore;

	private TraceChecker mTraceChecker;
	private IInterpolantGenerator mInterpolantGenerator;
	private IInterpolantAutomatonBuilder<LETTER, IPredicate> mInterpolantAutomatonBuilder;
	private final int mIteration;
	private final CegarLoopStatisticsGenerator mCegarLoopsBenchmark;

	/**
	 * @param context
	 *            context
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param counterexample
	 *            counterexample trace
	 * @param abstraction
	 *            abstraction
	 * @param iteration
	 *            current CEGAR loop iteration
	 * @param cegarLoopBenchmarks
	 *            benchmark
	 */
	@SuppressWarnings("squid:S1699")
	public MultiTrackTraceAbstractionRefinementStrategy(final StrategyContext<LETTER> context,
			final PredicateUnifier predicateUnifier, final IRun<LETTER, IPredicate, ?> counterexample,
			final IAutomaton<LETTER, IPredicate> abstraction, final int iteration,
			final CegarLoopStatisticsGenerator cegarLoopBenchmarks) {
		mContext = context;
		mCounterexample = counterexample;
		mAbstraction = abstraction;
		mPredicateUnifier = predicateUnifier;
		mIteration = iteration;
		mCegarLoopsBenchmark = cegarLoopBenchmarks;

		mInterpolationTechniques = initializeInterpolationTechniquesList();
		mNextTechnique = mInterpolationTechniques.next();
	}

	@Override
	public boolean hasNextTraceChecker() {
		return mInterpolationTechniques.hasNext();
	}

	@Override
	public void nextTraceChecker() {
		if (mNextTechnique != null) {
			throw new UnsupportedOperationException("Try the existing combination before advancing.");
		}
		mNextTechnique = mInterpolationTechniques.next();

		// reset trace checker, interpolant generator, and constructor
		mTraceChecker = null;
		mInterpolantGenerator = null;
		mPrevTcConstructor = mTcConstructor;
		mTcConstructor = null;

		mContext.getLogger().info("Switched to mode " + mNextTechnique);
	}

	@Override
	public TraceChecker getTraceChecker() {
		if (mTraceChecker == null) {
			if (mTcConstructor == null) {
				mTcConstructor = constructTraceCheckerConstructor();
			}
			mTraceChecker = mTcConstructor.get();
		}
		return mTraceChecker;
	}

	@Override
	public boolean hasNextInterpolantGenerator(final List<InterpolantsPreconditionPostcondition> perfectIpps,
			final List<InterpolantsPreconditionPostcondition> imperfectIpps) {
		if (!hasNextInterpolantGeneratorAvailable()) {
			return false;
		}

		/*
		 * current policy: stop after finding at least one perfect interpolant sequence or at least two interpolant
		 * sequences in total
		 */
		if (!perfectIpps.isEmpty()) {
			return false;
		}
		return imperfectIpps.size() < INTERPOLANT_ACCEPTANCE_THRESHOLD;
	}

	protected boolean hasNextInterpolantGeneratorAvailable() {
		return mInterpolationTechniques.hasNext();
	}

	@Override
	public void nextInterpolantGenerator() {
		nextTraceChecker();
	}

	@Override
	public IInterpolantGenerator getInterpolantGenerator() {
		mHasShownInfeasibilityBefore = true;
		if (mInterpolantGenerator == null) {
			mInterpolantGenerator = RefinementStrategyUtils.constructInterpolantGenerator(mContext, getTraceChecker(),
					mPredicateUnifier, mCounterexample, mCegarLoopsBenchmark);
		}
		return mInterpolantGenerator;
	}

	@Override
	public IInterpolantAutomatonBuilder<LETTER, IPredicate> getInterpolantAutomatonBuilder(
			final List<InterpolantsPreconditionPostcondition> perfectIpps,
			final List<InterpolantsPreconditionPostcondition> imperfectIpps) {
		// current policy: use all interpolant sequences
		final List<InterpolantsPreconditionPostcondition> allIpps =
				IRefinementStrategy.wrapTwoListsInOne(perfectIpps, imperfectIpps);

		if (mInterpolantAutomatonBuilder == null) {
			mInterpolantAutomatonBuilder = new MultiTrackInterpolantAutomatonBuilder<>(mContext.getServices(),
					mCounterexample, allIpps, mAbstraction);
		}
		return mInterpolantAutomatonBuilder;
	}

	/**
	 * @return iterator of different combinations.
	 */
	protected abstract Iterator<Track> initializeInterpolationTechniquesList();

	private TraceCheckerConstructor<LETTER> constructTraceCheckerConstructor() {
		final InterpolationTechnique interpolationTechnique = getInterpolationTechnique(mNextTechnique);

		final boolean useTimeout = mHasShownInfeasibilityBefore;
		final ManagedScript managedScript =
				constructManagedScript(mContext.getServices(), mContext.getPrefs(), mNextTechnique, useTimeout);

		final AssertCodeBlockOrder assertionOrder =
				mContext.getAssertionOrderModulation().reportAndGet(mCounterexample, interpolationTechnique);

		mNextTechnique = null;

		TraceCheckerConstructor<LETTER> result;
		if (mPrevTcConstructor == null) {
			result = new TraceCheckerConstructor<>(mContext.getPrefs(), managedScript, mContext.getServices(),
					mPredicateUnifier, mCounterexample, assertionOrder, interpolationTechnique, mIteration,
					mCegarLoopsBenchmark);
		} else {
			result = new TraceCheckerConstructor<>(mPrevTcConstructor, managedScript, assertionOrder,
					interpolationTechnique, mCegarLoopsBenchmark);
		}

		return result;
	}

	private static InterpolationTechnique getInterpolationTechnique(final Track mode) {
		final InterpolationTechnique interpolationTechnique;
		switch (mode) {
		case SMTINTERPOL_TREE_INTERPOLANTS:
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
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
		return interpolationTechnique;
	}

	@SuppressWarnings("squid:S1151")
	private ManagedScript constructManagedScript(final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences prefs, final Track mode, final boolean useTimeout) {
		final boolean dumpSmtScriptToFile = prefs.getDumpSmtScriptToFile();
		final String pathOfDumpedScript = prefs.getPathOfDumpedScript();
		final String baseNameOfDumpedScript =
				"Script_" + prefs.getIcfgContainer().getIdentifier() + "_Iteration" + mIteration;
		final Settings solverSettings;
		final SolverMode solverMode;
		final String logicForExternalSolver;
		final String command;
		switch (mode) {
		case SMTINTERPOL_TREE_INTERPOLANTS:
		case SMTINTERPOL_FP:
			final long timeout = useTimeout ? TIMEOUT_SMTINTERPOL : TIMEOUT_NONE_SMTINTERPOL;
			solverSettings = new Settings(false, false, null, timeout, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.Internal_SMTInterpol;
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
			command = useTimeout ? COMMAND_Z3_TIMEOUT : COMMAND_Z3_NO_TIMEOUT;
			solverSettings = new Settings(false, true, command, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
			logicForExternalSolver = LOGIC_Z3;
			break;
		case CVC4_FPBP:
		case CVC4_FP:
			command = useTimeout ? COMMAND_CVC4_TIMEOUT : COMMAND_CVC4_NO_TIMEOUT;
			solverSettings = new Settings(false, true, command, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
			logicForExternalSolver = getCvc4Logic();
			break;
		case MATHSAT_FPBP:
		case MATHSAT_FP:
			command = COMMAND_MATHSAT;
			solverSettings = new Settings(false, true, command, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
			logicForExternalSolver = LOGIC_MATHSAT;
			break;
		default:
			throw new IllegalArgumentException(
					"Managed script construction not supported for interpolation technique: " + mode);
		}
		final Script solver = SolverBuilder.buildAndInitializeSolver(services, prefs.getToolchainStorage(), solverMode,
				solverSettings, false, false, logicForExternalSolver, "TraceCheck_Iteration" + mIteration);
		final ManagedScript result = new ManagedScript(services, solver);

		final TermTransferrer tt = new TermTransferrer(solver);
		final Term axioms = prefs.getIcfgContainer().getCfgSmtToolkit().getAxioms().getFormula();
		solver.assertTerm(tt.transform(axioms));

		return result;
	}

	/**
	 * @return Logic string used for {@code CVC4}.
	 */
	protected abstract String getCvc4Logic();

	@Override
	public PredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public RefinementStrategyExceptionBlacklist getExceptionBlacklist() {
		return mContext.getPrefs().getExceptionBlacklist();
	}
}
