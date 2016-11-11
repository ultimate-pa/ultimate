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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.InterpolantAutomatonBuilderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerPathInvariantsWithFallback;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;

/**
 * Checks a trace for feasibility and, if infeasible, selects a refinement strategy, i.e., constructs an interpolant
 * automaton.<br>
 * This class is used in the {@link BasicCegarLoop}.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class TraceCheckAndRefinementSelection {
	/* inputs */
	
	/**
	 * Logger.
	 */
	private final ILogger mLogger;
	/**
	 * Ultimate services.
	 */
	private final IUltimateServiceProvider mServices;
	/**
	 * Trace abstraction preferences.
	 */
	private final TAPreferences mTaPrefs;
	/**
	 * Intermediate layer to encapsulate communication with SMT solvers.
	 */
	private final CfgSmtToolkit mCsToolkit;
	/**
	 * Predicate factory.
	 */
	private final PredicateFactory mPredicateFactory;
	/**
	 * Node of a recursive control flow graph which stores additional information about the program.
	 */
	private final BoogieIcfgContainer mIcfgContainer;
	
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final InterpolationTechnique mInterpolation;
	private final IToolchainStorage mToolchainStorage;
	private final CegarLoopStatisticsGenerator mCegarLoopBenchmark;
	private final InterpolantAutomatonBuilderFactory mInterpolantAutomatonBuilderFactory;
	/**
	 * Current Iteration of the CEGAR loop.
	 */
	private final int mIteration;
	
	/* preferences created from input settings */
	
	private final IPreferenceProvider mGeneralPrefs;
	private final AssertCodeBlockOrder mAssertCodeBlocksIncrementally;
	private final UnsatCores mUnsatCores;
	private final boolean mUseLiveVariables;
	private final boolean mUseInterpolantConsolidation;
	
	/* outputs */
	
	/**
	 * Feasibility status that was determined for the counterexample.
	 */
	private LBool mFeasibility;
	/**
	 * Interpolant automaton that was constructed.
	 */
	private NestedWordAutomaton<CodeBlock, IPredicate> mInterpolantAutomaton;
	/**
	 * Interpolant generator that was used.
	 */
	private IInterpolantGenerator mInterpolantGenerator;
	/**
	 * Interpolating trace checker.
	 */
	private InterpolatingTraceChecker mInterpolatingTraceChecker;
	/**
	 * Predicate unifier.
	 */
	private final PredicateUnifier mPredicateUnifier;
	/**
	 * Hoare triple checker that was used.
	 */
	private IHoareTripleChecker mHoareTripleChecker;
	
	public TraceCheckAndRefinementSelection(final IUltimateServiceProvider services, final ILogger logger,
			final TAPreferences taPrefs, final CfgSmtToolkit cfgSmtToolkit, final PredicateFactory predicateFactory,
			final BoogieIcfgContainer icfgContainer, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final InterpolationTechnique interpolation,
			final IToolchainStorage toolchainStorage, final CegarLoopStatisticsGenerator cegarLoopBenchmark,
			final InterpolantAutomatonBuilderFactory interpolantAutomatonBuilderFactory, final int iteration,
			final IRun<CodeBlock, IPredicate, ?> counterexample,
			final IAutomaton<CodeBlock, IPredicate> abstraction) throws AutomataOperationCanceledException {
		// initialize settings etc. (TODO move this to a preference factory)
		mServices = services;
		mLogger = logger;
		mTaPrefs = taPrefs;
		mCsToolkit = cfgSmtToolkit;
		mPredicateFactory = predicateFactory;
		mIcfgContainer = icfgContainer;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mInterpolation = interpolation;
		mToolchainStorage = toolchainStorage;
		mCegarLoopBenchmark = cegarLoopBenchmark;
		mInterpolantAutomatonBuilderFactory = interpolantAutomatonBuilderFactory;
		mIteration = iteration;
		
		mGeneralPrefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mAssertCodeBlocksIncrementally =
				mGeneralPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY,
						AssertCodeBlockOrder.class);
		mUnsatCores = mGeneralPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES, UnsatCores.class);
		mUseLiveVariables = mGeneralPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_LIVE_VARIABLES);
		mUseInterpolantConsolidation =
				mGeneralPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANTS_CONSOLIDATION);
		
		mPredicateUnifier = new PredicateUnifier(mServices, mCsToolkit.getManagedScript(),
				mPredicateFactory, mIcfgContainer.getBoogie2SMT().getBoogie2SmtSymbolTable(),
				mSimplificationTechnique, mXnfConversionTechnique);
		
		// check counterexample feasibility
		checkCounterexampleFeasibility(counterexample);
		
		// construct interpolant automaton depending on feasibility
		if (mFeasibility == LBool.UNSAT) {
			constructInterpolantAutomaton(counterexample, abstraction);
		}
	}
	
	public LBool getCounterexampleFeasibility() {
		return mFeasibility;
	}
	
	public NestedWordAutomaton<CodeBlock, IPredicate> getInterpolantAutomaton() {
		if (mInterpolantAutomaton == null) {
			throw new UnsupportedOperationException("There is no interpolant automaton.");
		}
		return mInterpolantAutomaton;
	}
	
	public IInterpolantGenerator getInterpolantGenerator() {
		return mInterpolantGenerator;
	}
	
	public InterpolatingTraceChecker getInterpolatingTraceChecker() {
		return mInterpolatingTraceChecker;
	}
	
	public PredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}
	
	public IHoareTripleChecker getHoareTripleChecker() {
		if (mHoareTripleChecker == null) {
			throw new UnsupportedOperationException("There is no Hoare triple checker.");
		}
		return mHoareTripleChecker;
	}
	
	private void checkCounterexampleFeasibility(final IRun<CodeBlock, IPredicate, ?> counterexample) {
		final FeasibilityCheckResult result;
		
		// TODO add several strategies here
		result = checkFeasibilityDefault(counterexample);
		
		// set fields feasibility
		mFeasibility = result.getFeasibility();
		mInterpolantGenerator = result.getInterpolantGenerator();
		mHoareTripleChecker = result.getHoareTripleChecker();
	}
	
	private FeasibilityCheckResult checkFeasibilityDefault(final IRun<CodeBlock, IPredicate, ?> counterexample) {
		final FeasibilityCheckResult result = new FeasibilityCheckResult();
		
		constructInterpolatingTraceChecker(counterexample);
		
		// check feasibility
		final LBool feasibility = mInterpolatingTraceChecker.isCorrect();
		result.setFeasibility(feasibility);
		
		if (feasibility != LBool.UNSAT) {
			// no infeasibility found, CEGAR loop is about to terminate
			return result;
		}
		
		// mTraceCheckerBenchmark.aggregateBenchmarkData(interpolatingTraceChecker.getTraceCheckerBenchmark());
		final IInterpolantGenerator interpolantGenerator = constructInterpolantGenerator(counterexample);
		result.setInterpolantGenerator(interpolantGenerator);
		
		// TODO set Hoare triple check and use it in BasicCegarLoop
		return result;
	}
	
	private ManagedScript setupManagedScript() throws AssertionError {
		final ManagedScript mgdScriptTc;
		if (mTaPrefs.useSeparateSolverForTracechecks()) {
			final String filename = mIcfgContainer.getFilename() + "_TraceCheck_Iteration" + mIteration;
			final SolverMode solverMode = mTaPrefs.solverMode();
			final boolean fakeNonIncrementalSolver = mTaPrefs.fakeNonIncrementalSolver();
			final String commandExternalSolver = mTaPrefs.commandExternalSolver();
			final boolean dumpSmtScriptToFile = mTaPrefs.dumpSmtScriptToFile();
			final String pathOfDumpedScript = mTaPrefs.pathOfDumpedScript();
			final Settings solverSettings = SolverBuilder.constructSolverSettings(filename, solverMode,
					fakeNonIncrementalSolver, commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
			final Script tcSolver = SolverBuilder.buildAndInitializeSolver(mServices, mToolchainStorage,
					mTaPrefs.solverMode(), solverSettings, false, false, mTaPrefs.logicForExternalSolver(),
					"TraceCheck_Iteration" + mIteration);
			mgdScriptTc = new ManagedScript(mServices, tcSolver);
			final TermTransferrer tt = new TermTransferrer(tcSolver);
			for (final Term axiom : mIcfgContainer.getBoogie2SMT().getAxioms()) {
				tcSolver.assertTerm(tt.transform(axiom));
			}
		} else {
			mgdScriptTc = mCsToolkit.getManagedScript();
		}
		return mgdScriptTc;
	}
	
	private void constructInterpolatingTraceChecker(final IRun<CodeBlock, IPredicate, ?> counterexample)
			throws AssertionError {
		final ManagedScript mgdScriptTc = setupManagedScript();
		
		mInterpolatingTraceChecker = constructTraceChecker(counterexample, mgdScriptTc);
		
		if (mInterpolatingTraceChecker.getToolchainCanceledExpection() != null) {
			throw mInterpolatingTraceChecker.getToolchainCanceledExpection();
		} else if (mTaPrefs.useSeparateSolverForTracechecks()) {
			mgdScriptTc.getScript().exit();
		}
	}
	
	private InterpolatingTraceChecker constructTraceChecker(final IRun<CodeBlock, IPredicate, ?> counterexample,
			final ManagedScript mgdScriptTc) {
		final IPredicate truePredicate = mPredicateUnifier.getTruePredicate();
		final IPredicate falsePredicate = mPredicateUnifier.getFalsePredicate();
		
		final InterpolatingTraceChecker interpolatingTraceChecker;
		switch (mInterpolation) {
			case Craig_NestedInterpolation:
			case Craig_TreeInterpolation:
				interpolatingTraceChecker = new InterpolatingTraceCheckerCraig(truePredicate, falsePredicate,
						new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(counterexample.getWord()),
						mCsToolkit, mAssertCodeBlocksIncrementally,
						mServices, true, mPredicateUnifier, mInterpolation, mgdScriptTc,
						true, mXnfConversionTechnique, mSimplificationTechnique, counterexample.getStateSequence(),
						false);
				break;
			case ForwardPredicates:
			case BackwardPredicates:
			case FPandBP:
				interpolatingTraceChecker = new TraceCheckerSpWp(truePredicate, falsePredicate,
						new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(counterexample.getWord()),
						mCsToolkit, mAssertCodeBlocksIncrementally,
						mUnsatCores, mUseLiveVariables, mServices, true, mPredicateUnifier, mInterpolation,
						mgdScriptTc, mXnfConversionTechnique, mSimplificationTechnique,
						counterexample.getStateSequence());
				
				break;
			case PathInvariants:
				final boolean useNonlinearConstraints = mGeneralPrefs.getBoolean(
						TraceAbstractionPreferenceInitializer.LABEL_NONLINEAR_CONSTRAINTS_IN_PATHINVARIANTS);
				final boolean useVarsFromUnsatCore = mGeneralPrefs
						.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES_IN_PATHINVARIANTS);
				final boolean dumpSmtScriptToFile = mTaPrefs.dumpSmtScriptToFile();
				final String pathOfDumpedScript = mTaPrefs.pathOfDumpedScript();
				final String baseNameOfDumpedScript =
						"InVarSynth_" + mIcfgContainer.getFilename() + "_Iteration" + mIteration;
				final String solverCommand;
				if (useNonlinearConstraints) {
					// solverCommand = "yices-smt2 --incremental";
					// solverCommand = "/home/matthias/ultimate/barcelogic/barcelogic-NIRA -tlimit 5";
					solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:42000";
					// solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:1000";
				} else {
					// solverCommand = "yices-smt2 --incremental";
					solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:42000";
				}
				final boolean fakeNonIncrementalSolver = false;
				final Settings settings = new Settings(fakeNonIncrementalSolver, true, solverCommand, -1, null,
						dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript);
				interpolatingTraceChecker =
						new InterpolatingTraceCheckerPathInvariantsWithFallback(truePredicate, falsePredicate,
								new TreeMap<Integer, IPredicate>(), (NestedRun<CodeBlock, IPredicate>) counterexample,
								mCsToolkit, mAssertCodeBlocksIncrementally, mServices,
								mToolchainStorage, true, mPredicateUnifier, useNonlinearConstraints,
								useVarsFromUnsatCore,
								settings, mXnfConversionTechnique,
								mSimplificationTechnique, mIcfgContainer.getBoogie2SMT().getAxioms());
				break;
			default:
				throw new UnsupportedOperationException("unsupported interpolation");
		}
		mCegarLoopBenchmark.addTraceCheckerData(interpolatingTraceChecker.getTraceCheckerBenchmark());
		return interpolatingTraceChecker;
	}
	
	private IInterpolantGenerator constructInterpolantGenerator(final IRun<CodeBlock, IPredicate, ?> counterexample)
			throws AssertionError {
		final IInterpolantGenerator interpolantGenerator;
		if (mUseInterpolantConsolidation) {
			try {
				interpolantGenerator = consolidateInterpolants(counterexample, mInterpolatingTraceChecker);
			} catch (final AutomataOperationCanceledException e) {
				// Timeout
				e.printStackTrace();
				throw new AssertionError("react on timeout, not yet implemented");
			}
		} else {
			interpolantGenerator = mInterpolatingTraceChecker;
		}
		return interpolantGenerator;
	}
	
	private IInterpolantGenerator consolidateInterpolants(final IRun<CodeBlock, IPredicate, ?> counterexample,
			final InterpolatingTraceChecker interpolatingTraceChecker) throws AutomataOperationCanceledException {
		final IInterpolantGenerator interpolantGenerator;
		final InterpolantConsolidation interpConsoli =
				new InterpolantConsolidation(mPredicateUnifier.getTruePredicate(),
						mPredicateUnifier.getFalsePredicate(), new TreeMap<Integer, IPredicate>(),
						NestedWord.nestedWord(counterexample.getWord()), mCsToolkit, mCsToolkit.getModifiableGlobals(),
						mServices, mLogger, mPredicateUnifier, interpolatingTraceChecker, mTaPrefs);
		// Add benchmark data of interpolant consolidation
		mCegarLoopBenchmark.addInterpolationConsolidationData(interpConsoli.getInterpolantConsolidationBenchmarks());
		interpolantGenerator = interpConsoli;
		return interpolantGenerator;
	}
	
	private void constructInterpolantAutomaton(final IRun<CodeBlock, IPredicate, ?> counterexample,
			final IAutomaton<CodeBlock, IPredicate> abstraction) throws AutomataOperationCanceledException {
		if (mFeasibility != LBool.UNSAT) {
			throw new UnsupportedOperationException(
					"Constructing an interpolant automaton requires infeasible counterexample.");
		}
		
		// TODO add several strategies here
		mInterpolantAutomaton = constructInterpolantAutomatonDefault(counterexample, abstraction);
	}
	
	private NestedWordAutomaton<CodeBlock, IPredicate> constructInterpolantAutomatonDefault(
			final IRun<CodeBlock, IPredicate, ?> counterexample, final IAutomaton<CodeBlock, IPredicate> abstraction)
			throws AutomataOperationCanceledException {
		final IInterpolantAutomatonBuilder<CodeBlock, IPredicate> builder =
				mInterpolantAutomatonBuilderFactory.createBuilder(abstraction, mInterpolantGenerator, counterexample);
		return builder.getResult();
	}
	
	/**
	 * Wrapper for the data of fields that are only initialized after the feasibility check has finished.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private static class FeasibilityCheckResult {
		private LBool mFeasibilityInner;
		private IHoareTripleChecker mHoareTripleCheckerInner;
		private IInterpolantGenerator mInterpolantGeneratorInner;
		
		public FeasibilityCheckResult() {
			// nothing to do
		}
		
		public LBool getFeasibility() {
			return mFeasibilityInner;
		}
		
		public IInterpolantGenerator getInterpolantGenerator() {
			return mInterpolantGeneratorInner;
		}
		
		public IHoareTripleChecker getHoareTripleChecker() {
			return mHoareTripleCheckerInner;
		}
		
		public void setFeasibility(final LBool isFeasible) {
			mFeasibilityInner = isFeasible;
		}
		
		public void setInterpolantGenerator(final IInterpolantGenerator interpolantGenerator) {
			mInterpolantGeneratorInner = interpolantGenerator;
		}
		
		public void setHoareTripleChecker(final IHoareTripleChecker hoareTripleChecker) {
			mHoareTripleCheckerInner = hoareTripleChecker;
		}
	}
}
