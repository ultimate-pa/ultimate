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
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.MultiTrackInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
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
public abstract class MultiTrackTraceAbstractionRefinementStrategy implements IRefinementStrategy {
	/**
	 * Possible tracks.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	protected enum Track {
		/**
		 * SMTInterpol with tree interpolation.
		 */
		SMTINTERPOL_TREE_INTERPOLANTS,
		/**
		 * Z3 with forward and backward predicates.
		 */
		Z3_FPBP,
		/**
		 * Z3 with Craig interpolation
		 */
		Z3_NESTED_INTERPOLANTS,
		/**
		 * CVC4 with forward and backward predicates.
		 */
		CVC4_FPBP
	}
	
	private static final String UNKNOWN_MODE = "Unknown mode: ";
	private static final String LOGIC_Z3 = "ALL";
	private static final int SMTINTERPOL_TIMEOUT = 10_000;
	// private static final String Z3_COMMAND = RcfgPreferenceInitializer.Z3_DEFAULT;
	private static final String Z3_COMMAND = "z3 -smt2 -in SMTLIB2_COMPLIANT=true";
	private static final String CVC4_COMMAND = "cvc4 --tear-down-incremental --print-success --lang smt";
	
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences mPrefs;
	private final AssertionOrderModulation mAssertionOrderModulation;
	private final IRun<CodeBlock, IPredicate, ?> mCounterexample;
	private final IAutomaton<CodeBlock, IPredicate> mAbstraction;
	private final PredicateUnifier mPredicateUnifier;
	
	// TODO Christian 2016-11-11: Matthias wants to get rid of this
	private final TAPreferences mTaPrefsForInterpolantConsolidation;
	
	private final Iterator<Track> mInterpolationTechniques;
	
	private TraceCheckerConstructor mTcConstructor;
	private TraceCheckerConstructor mPrevTcConstructor;
	private Track mNextTechnique;
	
	private TraceChecker mTraceChecker;
	private IInterpolantGenerator mInterpolantGenerator;
	private IInterpolantAutomatonBuilder<CodeBlock, IPredicate> mInterpolantAutomatonBuilder;
	private final int mIteration;
	private final CegarLoopStatisticsGenerator mCegarLoopsBenchmark;
	
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
	 * @param abstraction
	 *            abstraction
	 * @param taPrefsForInterpolantConsolidation
	 *            temporary argument, should be removed
	 */
	public MultiTrackTraceAbstractionRefinementStrategy(final ILogger logger,
			final TaCheckAndRefinementPreferences prefs, final IUltimateServiceProvider services,
			final PredicateUnifier predicateUnifier, final AssertionOrderModulation assertionOrderModulation,
			final IRun<CodeBlock, IPredicate, ?> counterexample, final IAutomaton<CodeBlock, IPredicate> abstraction,
			final TAPreferences taPrefsForInterpolantConsolidation, final int iteration,
			final CegarLoopStatisticsGenerator cegarLoopBenchmarks) {
		mServices = services;
		mLogger = logger;
		mPrefs = prefs;
		mAssertionOrderModulation = assertionOrderModulation;
		mCounterexample = counterexample;
		mAbstraction = abstraction;
		mPredicateUnifier = predicateUnifier;
		mIteration = iteration;
		mCegarLoopsBenchmark = cegarLoopBenchmarks;
		mTaPrefsForInterpolantConsolidation = taPrefsForInterpolantConsolidation;
		mInterpolationTechniques = initializeInterpolationTechniquesList();
		mNextTechnique = mInterpolationTechniques.next();
	}
	
	@Override
	public boolean hasNext(final RefinementStrategyAdvance advance) {
		switch (advance) {
			case TRACE_CHECKER:
			case INTERPOLANT_GENERATOR:
				return mInterpolationTechniques.hasNext();
			default:
				throw new IllegalArgumentException(UNKNOWN_MODE + advance);
		}
	}
	
	@Override
	public void next(final RefinementStrategyAdvance advance) {
		switch (advance) {
			case TRACE_CHECKER:
			case INTERPOLANT_GENERATOR:
				if (mNextTechnique != null) {
					throw new UnsupportedOperationException("Try the existing combination before advancing.");
				}
				mNextTechnique = mInterpolationTechniques.next();
				
				// reset trace checker, interpolant generator, and constructor
				mTraceChecker = null;
				mInterpolantGenerator = null;
				mPrevTcConstructor = mTcConstructor;
				mTcConstructor = null;
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
			mInterpolantGenerator = constructInterpolantGenerator(getTraceChecker());
		}
		return mInterpolantGenerator;
	}
	
	@Override
	public IInterpolantAutomatonBuilder<CodeBlock, IPredicate>
			getInterpolantAutomatonBuilder(final List<InterpolantsPreconditionPostcondition> ipps) {
		if (mInterpolantAutomatonBuilder == null) {
			mInterpolantAutomatonBuilder =
					new MultiTrackInterpolantAutomatonBuilder(mServices, mCounterexample, ipps, mAbstraction);
		}
		return mInterpolantAutomatonBuilder;
	}
	
	protected abstract Iterator<Track> initializeInterpolationTechniquesList();
	
	private TraceCheckerConstructor constructTraceCheckerConstructor() {
		final InterpolationTechnique interpolationTechnique = getInterpolationTechnique(mNextTechnique);
		
		final ManagedScript managedScript = constructManagedScript(mServices, mPrefs, mNextTechnique);
		
		final AssertCodeBlockOrder assertionOrder = mAssertionOrderModulation.reportAndGet(mCounterexample);
		
		mNextTechnique = null;
		
		TraceCheckerConstructor result;
		if (mPrevTcConstructor == null) {
			result = new TraceCheckerConstructor(mPrefs, managedScript, mServices, mPredicateUnifier, mCounterexample,
					assertionOrder, interpolationTechnique, mIteration, mCegarLoopsBenchmark);
		} else {
			result = new TraceCheckerConstructor(mPrevTcConstructor, managedScript, assertionOrder,
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
				interpolationTechnique = InterpolationTechnique.FPandBP;
				break;
			default:
				throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
		return interpolationTechnique;
	}
	
	private ManagedScript constructManagedScript(final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences prefs, final Track mode) {
		final boolean dumpSmtScriptToFile = prefs.getDumpSmtScriptToFile();
		final String pathOfDumpedScript = prefs.getPathOfDumpedScript();
		final String baseNameOfDumpedScript =
				"Script_" + prefs.getIcfgContainer().getIdentifier() + "_Iteration" + mIteration;
		final Settings solverSettings;
		final SolverMode solverMode;
		final String logicForExternalSolver;
		switch (mode) {
			case SMTINTERPOL_TREE_INTERPOLANTS:
				solverSettings = new Settings(false, false, null, SMTINTERPOL_TIMEOUT, null, dumpSmtScriptToFile,
						pathOfDumpedScript, baseNameOfDumpedScript);
				solverMode = SolverMode.Internal_SMTInterpol;
				logicForExternalSolver = null;
				break;
			case Z3_NESTED_INTERPOLANTS:
				solverSettings = new Settings(false, true, Z3_COMMAND, 0, /* TODO: Add external interpolator */
						null, dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript);
				solverMode = SolverMode.External_Z3InterpolationMode;
				logicForExternalSolver = LOGIC_Z3;
				break;
			case Z3_FPBP:
				solverSettings = new Settings(false, true, Z3_COMMAND, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
						baseNameOfDumpedScript);
				solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
				logicForExternalSolver = LOGIC_Z3;
				break;
			case CVC4_FPBP:
				solverSettings =
						new Settings(false, true, CVC4_COMMAND, 0, null, dumpSmtScriptToFile, pathOfDumpedScript,
								baseNameOfDumpedScript);
				solverMode = SolverMode.External_ModelsAndUnsatCoreMode;
				logicForExternalSolver = getCvc4Logic();
				break;
			default:
				throw new IllegalArgumentException(
						"Managed script construction not supported for interpolation technique: " + mode);
		}
		final Script solver = SolverBuilder.buildAndInitializeSolver(services, prefs.getToolchainStorage(), solverMode,
				solverSettings, false, false, logicForExternalSolver, "TraceCheck_Iteration" + mIteration);
		final ManagedScript result = new ManagedScript(services, solver);
		
		// TODO do we need this?
		final TermTransferrer tt = new TermTransferrer(solver);
		for (final Term axiom : prefs.getIcfgContainer().getCfgSmtToolkit().getAxioms()) {
			solver.assertTerm(tt.transform(axiom));
		}
		
		return result;
	}
	
	/**
	 * @return Logic string used for {@code CVC4}.
	 */
	protected abstract String getCvc4Logic();
	
	/**
	 * TODO Refactor this code duplicate with {@link FixedTraceAbstractionRefinementStrategy}.
	 */
	private IInterpolantGenerator constructInterpolantGenerator(final TraceChecker tracechecker) {
		final TraceChecker localTraceChecker = Objects.requireNonNull(tracechecker,
				"cannot construct interpolant generator if no trace checker is present");
		if (localTraceChecker instanceof InterpolatingTraceChecker) {
			final InterpolatingTraceChecker interpolatingTraceChecker = (InterpolatingTraceChecker) localTraceChecker;
			
			if (mPrefs.getUseInterpolantConsolidation()) {
				try {
					return consolidateInterpolants(interpolatingTraceChecker);
				} catch (final AutomataOperationCanceledException e) {
					throw new AssertionError("react on timeout, not yet implemented");
				}
			}
			return interpolatingTraceChecker;
		}
		// TODO insert code here to support generating interpolants from a different source
		throw new AssertionError("Currently only interpolating trace checkers are supported.");
	}
	
	/**
	 * TODO Refactor this code duplicate with {@link FixedTraceAbstractionRefinementStrategy}.
	 */
	private IInterpolantGenerator consolidateInterpolants(final InterpolatingTraceChecker interpolatingTraceChecker)
			throws AutomataOperationCanceledException {
		final CfgSmtToolkit cfgSmtToolkit = mPrefs.getCfgSmtToolkit();
		final InterpolantConsolidation interpConsoli = new InterpolantConsolidation(
				mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
				new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(mCounterexample.getWord()), cfgSmtToolkit,
				cfgSmtToolkit.getModifiableGlobalsTable(), mServices, mLogger, mPredicateUnifier,
				interpolatingTraceChecker, mTaPrefsForInterpolantConsolidation);
		// Add benchmark data of interpolant consolidation
		mCegarLoopsBenchmark.addInterpolationConsolidationData(interpConsoli.getInterpolantConsolidationBenchmarks());
		return interpConsoli;
	}
	
	@Override
	public PredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}
	
	@Override
	public RefinementStrategyExceptionBlacklist getExceptionBlacklist() {
		return mPrefs.getExceptionBlacklist();
	}
}
