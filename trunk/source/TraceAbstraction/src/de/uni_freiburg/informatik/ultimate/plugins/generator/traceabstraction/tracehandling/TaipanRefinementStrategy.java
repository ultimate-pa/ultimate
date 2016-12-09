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

import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.MultiTrackInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * {@link IRefinementStrategy} that is used by Taipan. It first tries an {@link InterpolatingTraceChecker} using
 * {@link SMTInterpol} with {@link InterpolationTechnique#Craig_TreeInterpolation}.<br>
 * If successful and the interpolant sequence is perfect, those interpolants are used.<br>
 * If not successful, it tries {@link TraceChecker} {@code Z3} and, if again not successful, {@code CVC4}.<br>
 * If none of those is successful, the strategy gives up.<br>
 * Otherwise, if the trace is infeasible, the strategy uses an {@link CegarAbsIntRunner} to construct interpolants.<br>
 * If not successful, the strategy again tries {@code Z3} and {@code CVC4}, but this time using interpolation
 * {@link InterpolationTechnique#FPandBP}.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class TaipanRefinementStrategy implements IRefinementStrategy {
	
	private static final String UNKNOWN_MODE = "Unknown mode: ";
	private static final int SMTINTERPOL_TIMEOUT = 10_000;
	private static final String LOGIC_FOR_EXTERNAL_SOLVERS = "AUFNIRA";
	private static final String Z3_COMMAND = "z3 -smt2 -in SMTLIB2_COMPLIANT=true";
	private static final String CVC4_COMMAND = "cvc4 --tear-down-incremental --print-success --lang smt";
	
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences mPrefs;
	private final PredicateUnifier mPredicateUnifier;
	private final CegarAbsIntRunner mAbsIntRunner;
	private final IRun<CodeBlock, IPredicate, ?> mCounterexample;
	private final IAutomaton<CodeBlock, IPredicate> mAbstraction;
	
	private Mode mCurrentMode;
	
	// if the first Z3 trace check was unsuccessful, we can skip it the second time
	private boolean mZ3TraceCheckUnsuccessful;
	
	private TraceCheckerConstructor mTcConstructor;
	private TraceCheckerConstructor mPrevTcConstructor;
	
	private TraceChecker mTraceChecker;
	private IInterpolantGenerator mInterpolantGenerator;
	private IInterpolantAutomatonBuilder<CodeBlock, IPredicate> mInterpolantAutomatonBuilder;
	private final int mIteration;
	private final CegarLoopStatisticsGenerator mCegarLoopBenchmark;
	
	public TaipanRefinementStrategy(final ILogger logger, final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences prefs, final PredicateUnifier predicateUnifier,
			final CegarAbsIntRunner absIntRunner, final IRun<CodeBlock, IPredicate, ?> counterexample,
			final IAutomaton<CodeBlock, IPredicate> abstraction, final int iteration,
			final CegarLoopStatisticsGenerator cegarLoopBenchmark) {
		mServices = services;
		mLogger = logger;
		mPrefs = prefs;
		mPredicateUnifier = predicateUnifier;
		mAbsIntRunner = absIntRunner;
		mCounterexample = counterexample;
		mAbstraction = abstraction;
		mIteration = iteration;
		mCurrentMode = Mode.SMTINTERPOL;
		mCegarLoopBenchmark = cegarLoopBenchmark;
	}
	
	@Override
	public boolean hasNext(final RefinementStrategyAdvance advance) {
		switch (advance) {
		case TRACE_CHECKER:
			switch (mCurrentMode) {
			case SMTINTERPOL:
			case Z3_NO_IG:
				return true;
			case CVC4_NO_IG:
			case ABSTRACT_INTERPRETATION:
			case Z3_IG:
			case CVC4_IG:
				return false;
			default:
				throw new IllegalArgumentException(UNKNOWN_MODE + mCurrentMode);
			}
		case INTERPOLANT_GENERATOR:
			switch (mCurrentMode) {
			case SMTINTERPOL:
			case ABSTRACT_INTERPRETATION:
			case Z3_IG:
				return true;
			case CVC4_IG:
			case Z3_NO_IG:
			case CVC4_NO_IG:
				return false;
			default:
				throw new IllegalArgumentException(UNKNOWN_MODE + mCurrentMode);
			}
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + advance);
		}
	}
	
	@Override
	public void next(final RefinementStrategyAdvance advance) {
		switch (advance) {
		case TRACE_CHECKER:
			switch (mCurrentMode) {
			case SMTINTERPOL:
				mCurrentMode = Mode.Z3_NO_IG;
				break;
			case Z3_NO_IG:
				mCurrentMode = Mode.CVC4_NO_IG;
				mZ3TraceCheckUnsuccessful = false;
				break;
			case CVC4_NO_IG:
			case ABSTRACT_INTERPRETATION:
			case Z3_IG:
			case CVC4_IG:
				assert !hasNext(advance);
				throw new NoSuchElementException("No next trace checker available.");
			default:
				throw new IllegalArgumentException(UNKNOWN_MODE + mCurrentMode);
			}
			
			// reset trace checker, interpolant generator, and constructor
			mTraceChecker = null;
			mInterpolantGenerator = null;
			mPrevTcConstructor = mTcConstructor;
			mTcConstructor = null;
			break;
		case INTERPOLANT_GENERATOR:
			final boolean resetTraceChecker;
			switch (mCurrentMode) {
			case SMTINTERPOL:
				mCurrentMode = Mode.ABSTRACT_INTERPRETATION;
				resetTraceChecker = false;
				break;
			case ABSTRACT_INTERPRETATION:
				if (mZ3TraceCheckUnsuccessful) {
					mCurrentMode = Mode.CVC4_IG;
				} else {
					mCurrentMode = Mode.Z3_IG;
				}
				resetTraceChecker = true;
				break;
			case Z3_IG:
				mCurrentMode = Mode.CVC4_IG;
				resetTraceChecker = true;
				break;
			case CVC4_IG:
			case Z3_NO_IG:
			case CVC4_NO_IG:
				assert !hasNext(advance);
				throw new NoSuchElementException("No next interpolant generator available.");
			default:
				throw new IllegalArgumentException(UNKNOWN_MODE + advance);
			}
			
			// reset interpolant generator
			mInterpolantGenerator = null;
			if (resetTraceChecker) {
				// reset trace checker and constructor
				mTraceChecker = null;
				mPrevTcConstructor = mTcConstructor;
				mTcConstructor = null;
			}
			break;
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + advance);
		}
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
	public IInterpolantGenerator getInterpolantGenerator() {
		if (mInterpolantGenerator == null) {
			mInterpolantGenerator = constructInterpolantGenerator(mCurrentMode);
		}
		return mInterpolantGenerator;
	}
	
	@Override
	public IInterpolantAutomatonBuilder<CodeBlock, IPredicate>
			getInterpolantAutomatonBuilder(final List<InterpolantsPreconditionPostcondition> ipps) {
		if (mInterpolantAutomatonBuilder == null) {
			mInterpolantAutomatonBuilder = constructInterpolantAutomatonBuilder(ipps, mCurrentMode);
		}
		return mInterpolantAutomatonBuilder;
	}
	
	private IInterpolantAutomatonBuilder<CodeBlock, IPredicate> constructInterpolantAutomatonBuilder(
			final List<InterpolantsPreconditionPostcondition> ipps, final Mode mode) {
		switch (mode) {
		case ABSTRACT_INTERPRETATION:
			return ((AiRunnerWrapper) mInterpolantGenerator).getInterpolantAutomatonBuilder();
		case SMTINTERPOL:
		case Z3_IG:
		case CVC4_IG:
			return new MultiTrackInterpolantAutomatonBuilder(mServices, mCounterexample, ipps, mAbstraction);
		case Z3_NO_IG:
		case CVC4_NO_IG:
			throw new AssertionError("The mode " + mode + " should be unreachable here.");
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
	}
	
	private TraceCheckerConstructor constructTraceCheckerConstructor() {
		final InterpolationTechnique interpolationTechnique = getInterpolationTechnique(mCurrentMode);
		
		final ManagedScript managedScript = constructManagedScript(mServices, mPrefs, mCurrentMode, mIteration);
		
		TraceCheckerConstructor result;
		if (mPrevTcConstructor == null) {
			result = new TraceCheckerConstructor(mPrefs, managedScript, mServices, mPredicateUnifier, mCounterexample,
					interpolationTechnique, mIteration, mCegarLoopBenchmark);
		} else {
			result = new TraceCheckerConstructor(mPrevTcConstructor, managedScript, interpolationTechnique,
					mCegarLoopBenchmark);
		}
		
		return result;
	}
	
	private static InterpolationTechnique getInterpolationTechnique(final Mode mode) {
		final InterpolationTechnique interpolationTechnique;
		switch (mode) {
		case SMTINTERPOL:
			interpolationTechnique = InterpolationTechnique.Craig_TreeInterpolation;
			break;
		case Z3_IG:
		case CVC4_IG:
			interpolationTechnique = InterpolationTechnique.FPandBP;
			break;
		case Z3_NO_IG:
		case CVC4_NO_IG:
		case ABSTRACT_INTERPRETATION:
			interpolationTechnique = null;
			break;
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
		return interpolationTechnique;
	}
	
	private static ManagedScript constructManagedScript(final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences prefs, final Mode mode, final int iteration) {
		final boolean dumpSmtScriptToFile = prefs.getDumpSmtScriptToFile();
		final String pathOfDumpedScript = prefs.getPathOfDumpedScript();
		final String baseNameOfDumpedScript =
				"Script_" + prefs.getIcfgContainer().getFilename() + "_Iteration" + iteration;
		final Settings solverSettings;
		final SolverMode solverMode;
		final String logicForExternalSolver;
		switch (mode) {
		case SMTINTERPOL:
			solverSettings = new Settings(false, false, null, SMTINTERPOL_TIMEOUT, null, dumpSmtScriptToFile,
					pathOfDumpedScript, baseNameOfDumpedScript);
			solverMode = SolverMode.Internal_SMTInterpol;
			logicForExternalSolver = null;
			break;
		case Z3_IG:
		case Z3_NO_IG:
			solverSettings = new Settings(false, true, Z3_COMMAND, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
			logicForExternalSolver = LOGIC_FOR_EXTERNAL_SOLVERS;
			break;
		case CVC4_IG:
		case CVC4_NO_IG:
			solverSettings = new Settings(false, true, CVC4_COMMAND, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
					baseNameOfDumpedScript);
			solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
			logicForExternalSolver = LOGIC_FOR_EXTERNAL_SOLVERS;
			break;
		case ABSTRACT_INTERPRETATION:
			return null;
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
		final Script solver = SolverBuilder.buildAndInitializeSolver(services, prefs.getToolchainStorage(), solverMode,
				solverSettings, false, false, logicForExternalSolver, "TraceCheck_Iteration" + iteration);
		final ManagedScript result = new ManagedScript(services, solver);
		
		// TODO do we need this?
		final TermTransferrer tt = new TermTransferrer(solver);
		for (final Term axiom : prefs.getIcfgContainer().getBoogie2SMT().getAxioms()) {
			solver.assertTerm(tt.transform(axiom));
		}
		
		return result;
	}
	
	private IInterpolantGenerator constructInterpolantGenerator(final Mode mode) {
		switch (mode) {
		case SMTINTERPOL:
		case CVC4_IG:
			return castTraceChecker();
		case Z3_IG:
			assert !mZ3TraceCheckUnsuccessful;
			return castTraceChecker();
		case Z3_NO_IG:
		case CVC4_NO_IG:
			mCurrentMode = Mode.ABSTRACT_INTERPRETATION;
			//$FALL-THROUGH$
		case ABSTRACT_INTERPRETATION:
			mAbsIntRunner.generateFixpoints(mCounterexample,
					(INestedWordAutomatonSimple<CodeBlock, IPredicate>) mAbstraction);
			return new AiRunnerWrapper(mAbsIntRunner);
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
	}
	
	private IInterpolantGenerator castTraceChecker() {
		final TraceChecker traceChecker = getTraceChecker();
		assert traceChecker != null && traceChecker instanceof InterpolatingTraceChecker;
		return (InterpolatingTraceChecker) traceChecker;
	}
	
	@Override
	public PredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}
	
	@Override
	public RefinementStrategyExceptionBlacklist getExceptionBlacklist() {
		return RefinementStrategyExceptionBlacklist.NONE;
	}
	
	private class AiRunnerWrapper implements IInterpolantGenerator {
		private final CegarAbsIntRunner mRunner;
		
		public AiRunnerWrapper(final CegarAbsIntRunner runner) {
			mRunner = runner;
		}
		
		@Override
		public IPredicate[] getInterpolants() {
			// return a fake sequence of interpolants
			return new IPredicate[0];
		}
		
		@Override
		public boolean isPerfectSequence() {
			return mRunner.hasShownInfeasibility();
		}
		
		public IInterpolantAutomatonBuilder<CodeBlock, IPredicate> getInterpolantAutomatonBuilder() {
			return mRunner.createInterpolantAutomatonBuilder(mPredicateUnifier,
					(INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction, mCounterexample);
		}
		
		@Override
		public IPredicate getPrecondition() {
			return mPredicateUnifier.getTruePredicate();
		}
		
		@Override
		public IPredicate getPostcondition() {
			return mPredicateUnifier.getFalsePredicate();
		}
		
		@Override
		public Map<Integer, IPredicate> getPendingContexts() {
			throw new UnsupportedOperationException();
		}
		
		@Override
		public PredicateUnifier getPredicateUnifier() {
			return mPredicateUnifier;
		}
		
		@Override
		public Word<? extends IAction> getTrace() {
			throw new UnsupportedOperationException();
		}
	}
	
	/**
	 * Current mode in this strategy.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private enum Mode {
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
