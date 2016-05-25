/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Automaton2UltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeDfaHopcroftPaper;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeIncompleteDfa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeNwaCombinator;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat.MinimizeNwaMaxSAT;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizeDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IntersectDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.BestApproximationDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.SelfloopDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.LineCoverageCalculator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.CanonicalInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.TotalInterpolationAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.TwoTrackInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EfficientHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerPathInvariantsWithFallback;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessProductAutomaton;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * Subclass of AbstractCegarLoop which provides all algorithms for checking safety (not termination).
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class BasicCegarLoop extends AbstractCegarLoop {

	private final static boolean DIFFERENCE_INSTEAD_OF_INTERSECTION = true;
	protected final static boolean REMOVE_DEAD_ENDS = true;
	protected final static boolean TRACE_HISTOGRAMmBAILOUT = false;

	protected HoareAnnotationFragments mHaf;

	protected final PredicateFactoryRefinement mStateFactoryForRefinement;
	protected final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	protected final PredicateFactoryResultChecking mPredicateFactoryResultChecking;

	protected boolean mFallbackToFpIfInterprocedural = true;
	protected final INTERPOLATION mInterpolation;
	protected final InterpolantAutomaton mInterpolantAutomatonConstructionProcedure;
	protected final UnsatCores mUnsatCores;
	protected final boolean mUseLiveVariables;

	protected final boolean mComputeHoareAnnotation;

	private final boolean mUseInterpolantConsolidation;

	protected final AssertCodeBlockOrder mAssertCodeBlocksIncrementally;

	private final AbstractInterpretationRunner mAbsIntRunner;

	private NestedWordAutomaton<WitnessEdge, WitnessNode> mWitnessAutomaton;

	// private IHoareTripleChecker mHoareTripleChecker;
	private final boolean mDoFaultLocalization;
	private HashSet<ProgramPoint> mHoareAnnotationPositions;

	public BasicCegarLoop(String name, RootNode rootNode, SmtManager smtManager, TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs, INTERPOLATION interpolation, boolean computeHoareAnnotation,
			IUltimateServiceProvider services, IToolchainStorage storage) {

		super(services, storage, name, rootNode, smtManager, taPrefs, errorLocs,
				services.getLoggingService().getLogger(Activator.PLUGIN_ID));
		mUseInterpolantConsolidation = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANTS_CONSOLIDATION);
		if (mFallbackToFpIfInterprocedural && rootNode.getRootAnnot().getEntryNodes().size() > 1) {
			if (interpolation == INTERPOLATION.FPandBP) {
				mLogger.info("fallback from FPandBP to FP because CFG is interprocedural");
				mInterpolation = INTERPOLATION.ForwardPredicates;
			} else {
				mInterpolation = interpolation;
			}
			if (mPref.interpolantAutomaton() == InterpolantAutomaton.TWOTRACK) {
				mInterpolantAutomatonConstructionProcedure = InterpolantAutomaton.CANONICAL;
			} else {
				mInterpolantAutomatonConstructionProcedure = mPref.interpolantAutomaton();
			}
		} else {
			mInterpolation = interpolation;
			mInterpolantAutomatonConstructionProcedure = mPref.interpolantAutomaton();
		}
		// InterpolationPreferenceChecker.check(Activator.s_PLUGIN_NAME, interpolation);
		mComputeHoareAnnotation = computeHoareAnnotation;
		if (mPref.getHoareAnnotationPositions() == HoareAnnotationPositions.LoopsAndPotentialCycles) {
			mHoareAnnotationPositions = new HashSet<ProgramPoint>();
			mHoareAnnotationPositions.addAll(rootNode.getRootAnnot().getLoopLocations().keySet());
			// mHoareAnnotationPositions.addAll(rootNode.getRootAnnot().getExitNodes().values());
			mHoareAnnotationPositions.addAll(rootNode.getRootAnnot().getPotentialCycleProgramPoints());
		}
		mHaf = new HoareAnnotationFragments(mLogger, mHoareAnnotationPositions, mPref.getHoareAnnotationPositions());
		mStateFactoryForRefinement = new PredicateFactoryRefinement(mRootNode.getRootAnnot().getProgramPoints(),
				super.mSmtManager, mPref, REMOVE_DEAD_ENDS && mComputeHoareAnnotation, mHaf,
				mHoareAnnotationPositions);
		mPredicateFactoryInterpolantAutomata = new PredicateFactoryForInterpolantAutomata(super.mSmtManager, mPref);

		mAssertCodeBlocksIncrementally = (mServices.getPreferenceProvider(Activator.PLUGIN_ID)).getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY,
				AssertCodeBlockOrder.class);

		mPredicateFactoryResultChecking = new PredicateFactoryResultChecking(smtManager);

		mCegarLoopBenchmark = new CegarLoopStatisticsGenerator();
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.OverallTime.toString());

		final IPreferenceProvider mPrefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mUnsatCores = mPrefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES, UnsatCores.class);
		mUseLiveVariables = mPrefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_LIVE_VARIABLES);
		mDoFaultLocalization = mPrefs
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS);

		if (mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_USE_ABSTRACT_INTERPRETATION)) {
			mAbsIntRunner = new AbstractInterpretationRunner(services, mCegarLoopBenchmark, rootNode);
		} else {
			mAbsIntRunner = null;
		}
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		final CFG2NestedWordAutomaton cFG2NestedWordAutomaton = new CFG2NestedWordAutomaton(mServices,
				mPref.interprocedural(), super.mSmtManager, mLogger);

		mAbstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(super.mRootNode, mStateFactoryForRefinement,
				super.mErrorLocs);
		if (mPref.getHoareAnnotationPositions() == HoareAnnotationPositions.LoopsAndPotentialCycles) {
			final INestedWordAutomaton<CodeBlock, IPredicate> nwa = (INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction;
			for (final IPredicate pred : nwa.getStates()) {
				for (final OutgoingCallTransition<CodeBlock, IPredicate> trans : nwa.callSuccessors(pred)) {
					mHoareAnnotationPositions.add(((ISLPredicate) pred).getProgramPoint());
					mHoareAnnotationPositions.add(((ISLPredicate) trans.getSucc()).getProgramPoint());
				}
			}
		}
		if (mWitnessAutomaton != null) {
			final WitnessProductAutomaton wpa = new WitnessProductAutomaton(mServices,
					(INestedWordAutomatonSimple<CodeBlock, IPredicate>) mAbstraction, mWitnessAutomaton,
					mSmtManager);
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), wpa)).getResult();
			mLogger.info("Full witness product has " + test.sizeInformation());
			mLogger.info(wpa.generateBadWitnessInformation());
			final LineCoverageCalculator origCoverage = new LineCoverageCalculator(mServices, mAbstraction);
			mAbstraction = (new RemoveDeadEnds<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), wpa))
					.getResult();
			new LineCoverageCalculator(mServices, mAbstraction, origCoverage).reportCoverage("Witness product");
		}
	}

	@Override
	protected boolean isAbstractionCorrect() throws AutomataOperationCanceledException {
		final INestedWordAutomatonOldApi<CodeBlock, IPredicate> abstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) mAbstraction;
		try {
			mCounterexample = (new IsEmpty<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
					abstraction)).getNestedRun();
		} catch (final AutomataOperationCanceledException e) {
			e.printStackTrace();
		}

		if (mCounterexample == null) {
			return true;
		}

		if (mAbsIntRunner != null) {
			mAbsIntRunner.generateFixpoints(mCounterexample, abstraction);
		}

		if (mPref.dumpAutomata()) {
			dumpNestedRun(mCounterexample, mIterationPW, mLogger);
		}
		// mRunAnalyzer = new RunAnalyzer(mCounterexample);
		mLogger.info("Found error trace");
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(mCounterexample.getWord());
		}
		final HistogramOfIterable<CodeBlock> traceHistogram = new HistogramOfIterable<CodeBlock>(mCounterexample.getWord());
		mCegarLoopBenchmark.reportTraceHistogramMaximum(traceHistogram.getVisualizationArray()[0]);
		if (mLogger.isInfoEnabled()) {
			mLogger.info("trace histogram " + traceHistogram.toString());
		}
		if (TRACE_HISTOGRAMmBAILOUT) {
			if (traceHistogram.getVisualizationArray()[0] > traceHistogram.getVisualizationArray().length) {
				throw new ToolchainCanceledException(getClass(),
						"bailout by trace histogram " + traceHistogram.toString());
			}
		}
		// s_Logger.info("Cutpoints: " + mRunAnalyzer.getCutpoints());
		// s_Logger.debug(mRunAnalyzer.getOccurence());
		return false;
	}

	@Override
	protected LBool isCounterexampleFeasible() {
		final PredicateUnifier predicateUnifier = new PredicateUnifier(mServices, mSmtManager);
		final IPredicate truePredicate = predicateUnifier.getTruePredicate();
		final IPredicate falsePredicate = predicateUnifier.getFalsePredicate();

		InterpolatingTraceChecker interpolatingTraceChecker = null;
		final SmtManager smtMangerTracechecks;
		if (mPref.useSeparateSolverForTracechecks()) {
			final String filename = mRootNode.getFilename() + "_TraceCheck_Iteration" + mIteration;
			final SolverMode solverMode = mPref.solverMode();
			final String commandExternalSolver = mPref.commandExternalSolver();
			final boolean dumpSmtScriptToFile = mPref.dumpSmtScriptToFile();
			final String pathOfDumpedScript = mPref.pathOfDumpedScript();
			final Settings solverSettings = SolverBuilder.constructSolverSettings(
					filename, solverMode, commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
			final Script tcSolver = SolverBuilder.buildAndInitializeSolver(mServices, mToolchainStorage,
					mPref.solverMode(), solverSettings, false,
					false, mPref.logicForExternalSolver(), "TraceCheck_Iteration" + mIteration);
			smtMangerTracechecks = new SmtManager(tcSolver, mRootNode.getRootAnnot().getBoogie2SMT(),
					mRootNode.getRootAnnot().getModGlobVarManager(), mServices, false,
					mRootNode.getRootAnnot().getManagedScript());
			final TermTransferrer tt = new TermTransferrer(tcSolver);
			for (final Term axiom : mRootNode.getRootAnnot().getBoogie2SMT().getAxioms()) {
				tcSolver.assertTerm(tt.transform(axiom));
			}
		} else {
			smtMangerTracechecks = mSmtManager;
		}

		final LBool feasibility;
		switch (mInterpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation: {
			interpolatingTraceChecker = new InterpolatingTraceCheckerCraig(truePredicate, falsePredicate,
					new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(mCounterexample.getWord()), mSmtManager,
					mRootNode.getRootAnnot().getModGlobVarManager(), mAssertCodeBlocksIncrementally, mServices, true,
					predicateUnifier, mInterpolation, smtMangerTracechecks, true);
		}
			break;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
			interpolatingTraceChecker = new TraceCheckerSpWp(truePredicate, falsePredicate,
					new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(mCounterexample.getWord()), mSmtManager,
					mRootNode.getRootAnnot().getModGlobVarManager(), mAssertCodeBlocksIncrementally, mUnsatCores,
					mUseLiveVariables, mServices, true, predicateUnifier, mInterpolation, smtMangerTracechecks);

			break;
		case PathInvariants: {
			final boolean useNonlinerConstraints = true;
			final boolean dumpSmtScriptToFile = mPref.dumpSmtScriptToFile();
			final String pathOfDumpedScript = mPref.pathOfDumpedScript();
			final String baseNameOfDumpedScript = "InVarSynth_" + mRootNode.getFilename() + "_Iteration" + mIteration;
			final String solverCommand;
			if (useNonlinerConstraints) {
				// solverCommand = "yices-smt2 --incremental";
				// solverCommand = "/home/matthias/ultimate/barcelogic/barcelogic-NIRA -tlimit 5";
				solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:42000";
				// solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:1000";
			} else {
				solverCommand = "yices-smt2 --incremental";
			}
			final Settings settings = new Settings(true,
					solverCommand, -1, null,
					dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript);
			interpolatingTraceChecker = new InterpolatingTraceCheckerPathInvariantsWithFallback(truePredicate,
					falsePredicate, new TreeMap<Integer, IPredicate>(),
					(NestedRun<CodeBlock, IPredicate>) mCounterexample, mSmtManager, mModGlobVarManager,
					mAssertCodeBlocksIncrementally, mServices, mToolchainStorage, true, predicateUnifier, useNonlinerConstraints, settings);
			}
			break;
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		mCegarLoopBenchmark.addTraceCheckerData(interpolatingTraceChecker.getTraceCheckerBenchmark());
		if (interpolatingTraceChecker.getToolchainCancelledExpection() != null) {
			throw interpolatingTraceChecker.getToolchainCancelledExpection();
		} else {
			if (mPref.useSeparateSolverForTracechecks()) {
				smtMangerTracechecks.getScript().exit();
			}
		}

		feasibility = interpolatingTraceChecker.isCorrect();
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample might be feasible");
			final NestedWord<CodeBlock> counterexample = NestedWord.nestedWord(mCounterexample.getWord());
			String indentation = "";
			indentation += "  ";
			for (int j = 0; j < counterexample.length(); j++) {
				// String stmts =
				// counterexample.getSymbol(j).getPrettyPrintedStatements();
				// System.out.println(indentation + stmts);
				// s_Logger.info(indentation + stmts);
				if (counterexample.isCallPosition(j)) {
					indentation += "    ";
				}
				if (counterexample.isReturnPosition(j)) {
					indentation = indentation.substring(0, indentation.length() - 4);
				}
			}
			mRcfgProgramExecution = interpolatingTraceChecker.getRcfgProgramExecution();
			if (mDoFaultLocalization && feasibility == LBool.SAT) {
				final CFG2NestedWordAutomaton cFG2NestedWordAutomaton = new CFG2NestedWordAutomaton(mServices,
						mPref.interprocedural(), super.mSmtManager, mLogger);
				final NestedWordAutomaton<CodeBlock, IPredicate> cfg = cFG2NestedWordAutomaton
						.getNestedWordAutomaton(super.mRootNode, mStateFactoryForRefinement, super.mErrorLocs);
				final FlowSensitiveFaultLocalizer a = new FlowSensitiveFaultLocalizer(mCounterexample,
						cfg, mServices, mSmtManager,
						mModGlobVarManager, predicateUnifier);
				mRcfgProgramExecution = mRcfgProgramExecution.addRelevanceInformation(a.getRelevanceInformation());
			}
			// s_Logger.info("Trace with values");
			// s_Logger.info(interpolatingTraceChecker.getRcfgProgramExecution());
		}
		mCegarLoopBenchmark.addTraceCheckerData(interpolatingTraceChecker.getTraceCheckerBenchmark());
		// mTraceCheckerBenchmark.aggregateBenchmarkData(interpolatingTraceChecker.getTraceCheckerBenchmark());
		mInterpolantGenerator = interpolatingTraceChecker;
		if (mUseInterpolantConsolidation) {
			try {
				final InterpolantConsolidation interpConsoli = new InterpolantConsolidation(truePredicate, falsePredicate,
						new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(mCounterexample.getWord()),
						mSmtManager, mRootNode.getRootAnnot().getModGlobVarManager(), mServices, mLogger,
						predicateUnifier, interpolatingTraceChecker, mPref);
				// Add benchmark data of interpolant consolidation
				mCegarLoopBenchmark
						.addInterpolationConsolidationData(interpConsoli.getInterpolantConsolidationBenchmarks());
				mInterpolantGenerator = interpConsoli;
			} catch (final AutomataOperationCanceledException e) {
				// Timeout
				e.printStackTrace();
			}
		}
		return feasibility;
	}

	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		if (mAbsIntRunner != null && mAbsIntRunner.hasShownInfeasibility()) {
			// if AI has shown infeasibility, construct an AI interpolant automaton instead of an SMT-based one
			mInterpolAutomaton = mAbsIntRunner.constructInterpolantAutomaton(
					mInterpolantGenerator.getPredicateUnifier(), mSmtManager,
					(INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction, mCounterexample);
		} else {
			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString());
			switch (mInterpolantAutomatonConstructionProcedure) {
			case CANONICAL: {
				final List<ProgramPoint> programPoints = CoverageAnalysis.extractProgramPoints(mCounterexample);
				final CanonicalInterpolantAutomatonBuilder iab = new CanonicalInterpolantAutomatonBuilder(mServices,
						mInterpolantGenerator, programPoints, new InCaReAlphabet<CodeBlock>(mAbstraction),
						mSmtManager, mPredicateFactoryInterpolantAutomata, mLogger);
				iab.analyze();
				mInterpolAutomaton = iab.getInterpolantAutomaton();
				mLogger.info("Interpolants " + mInterpolAutomaton.getStates());

				// mCegarLoopBenchmark.addBackwardCoveringInformation(iab.getBackwardCoveringInformation());
				final BackwardCoveringInformation bci = TraceCheckerUtils.computeCoverageCapability(mServices,
						mInterpolantGenerator, programPoints, mLogger);
				mCegarLoopBenchmark.addBackwardCoveringInformation(bci);
			}
				break;
			case SINGLETRACE: {
				final StraightLineInterpolantAutomatonBuilder iab = new StraightLineInterpolantAutomatonBuilder(mServices,
						new InCaReAlphabet<CodeBlock>(mAbstraction), mInterpolantGenerator,
						mPredicateFactoryInterpolantAutomata);
				mInterpolAutomaton = iab.getResult();
			}
				break;
			case TOTALINTERPOLATION:
				throw new AssertionError("not supported by this CegarLoop");
			case TWOTRACK: {
				if (!(mInterpolantGenerator instanceof TraceCheckerSpWp)
						&& !(mInterpolantGenerator instanceof InterpolantConsolidation)) {
					throw new AssertionError("TWOTRACK only for TraceCheckerSpWp or InterpolantConsolidation");
				}
				final List<IPredicate> predicatesA;
				final List<IPredicate> predicatesB;
				boolean build2TrackAutomaton = false;
				if (mInterpolantGenerator instanceof TraceCheckerSpWp) {
					final TraceCheckerSpWp traceChecker = (TraceCheckerSpWp) mInterpolantGenerator;
					predicatesA = traceChecker.getForwardPredicates();
					predicatesB = traceChecker.getBackwardPredicates();
					build2TrackAutomaton = true;
				} else if (!((InterpolantConsolidation) mInterpolantGenerator).consolidationSuccessful()) {
					// if consolidation wasn't successful, then build a 2-Track-Automaton
					final InterpolantConsolidation ic = (InterpolantConsolidation) mInterpolantGenerator;
					predicatesA = ic.getInterpolantsOfType_I();
					predicatesB = ic.getInterpolantsOfType_II();
					build2TrackAutomaton = true;
				} else {
					predicatesA = null;
					predicatesB = null;
				}
				if (build2TrackAutomaton) {
					final TwoTrackInterpolantAutomatonBuilder ttiab = new TwoTrackInterpolantAutomatonBuilder(mServices,
							mCounterexample, mSmtManager, predicatesA, predicatesB,
							mInterpolantGenerator.getPrecondition(), mInterpolantGenerator.getPostcondition(),
							mAbstraction);
					mInterpolAutomaton = ttiab.getResult();
				} else {
					// Case of Canonical_Automaton, i.e. if the consolidation was successful
					// FIXME: The case TWOTRACK from the switch is not nice. Should be refactored!
					final List<ProgramPoint> programPoints = CoverageAnalysis.extractProgramPoints(mCounterexample);
					final CanonicalInterpolantAutomatonBuilder iab = new CanonicalInterpolantAutomatonBuilder(mServices,
							mInterpolantGenerator, programPoints, new InCaReAlphabet<CodeBlock>(mAbstraction),
							mSmtManager, mPredicateFactoryInterpolantAutomata, mLogger);
					iab.analyze();
					mInterpolAutomaton = iab.getInterpolantAutomaton();
					mLogger.info("Interpolants " + mInterpolAutomaton.getStates());

					// mCegarLoopBenchmark.addBackwardCoveringInformation(iab.getBackwardCoveringInformation());
					final BackwardCoveringInformation bci = TraceCheckerUtils.computeCoverageCapability(mServices,
							mInterpolantGenerator, programPoints, mLogger);
					mCegarLoopBenchmark.addBackwardCoveringInformation(bci);
				}
				break;
			}
			case TOTALINTERPOLATION2: {
				final INestedWordAutomaton<CodeBlock, IPredicate> abstraction = (INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction;
				final NestedRun<CodeBlock, IPredicate> counterexample = (NestedRun<CodeBlock, IPredicate>) mCounterexample;
				final TotalInterpolationAutomatonBuilder iab = new TotalInterpolationAutomatonBuilder(abstraction,
						counterexample.getStateSequence(), mInterpolantGenerator, mSmtManager,
						mPredicateFactoryInterpolantAutomata, mRootNode.getRootAnnot().getModGlobVarManager(),
						mInterpolation, mServices, mPref.getHoareTripleChecks());
				mInterpolAutomaton = iab.getResult();
				mCegarLoopBenchmark.addTotalInterpolationData(iab.getTotalInterpolationBenchmark());
			}
				break;
			}
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString());

			assert (accepts(mServices, mInterpolAutomaton,
					mCounterexample.getWord())) : "Interpolant automaton broken!";
			assert (new InductivityCheck(mServices, mInterpolAutomaton, false, true,
					new IncrementalHoareTripleChecker(mRootNode.getRootAnnot().getManagedScript(), mModGlobVarManager,
							mSmtManager.getBoogie2Smt()))).getResult();
		}
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		final PredicateUnifier predUnifier = mInterpolantGenerator.getPredicateUnifier();
		if (mAbsIntRunner != null) {
			if (mAbsIntRunner.hasShownInfeasibility()) {
				return mAbsIntRunner.refine(predUnifier, mInterpolAutomaton, mCounterexample,
						this::refineWithGivenAutomaton);
			}
			mAbsIntRunner.refineAnyways(predUnifier, mSmtManager,
					(INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction, mCounterexample,
					this::refineWithGivenAutomaton);
		}
		return refineWithGivenAutomaton(mInterpolAutomaton, predUnifier);
	}

	private boolean refineWithGivenAutomaton(NestedWordAutomaton<CodeBlock, IPredicate> interpolAutomaton,
			PredicateUnifier predicateUnifier)
			throws AssertionError, AutomataOperationCanceledException, AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(super.mIteration);
		// howDifferentAreInterpolants(interpolAutomaton.getStates());

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final boolean explointSigmaStarConcatOfIA = !mComputeHoareAnnotation;

		final INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldAbstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) mAbstraction;
		// Map<IPredicate, Set<IPredicate>> removedDoubleDeckers = null;
		// Map<IPredicate, IPredicate> context2entry = null;

		final CachingHoareTripleChecker htc;
		if (mInterpolantGenerator instanceof InterpolantConsolidation) {
			htc = ((InterpolantConsolidation) mInterpolantGenerator).getHoareTripleChecker();
		} else {
			final IHoareTripleChecker ehtc = getEfficientHoareTripleChecker(mServices, mPref.getHoareTripleChecks(),
					mSmtManager, mModGlobVarManager, mInterpolantGenerator.getPredicateUnifier());
			htc = new CachingHoareTripleChecker(ehtc, mInterpolantGenerator.getPredicateUnifier());
		}
		try {
			if (DIFFERENCE_INSTEAD_OF_INTERSECTION) {
				mLogger.debug("Start constructing difference");
				// assert(oldAbstraction.getStateFactory() ==
				// interpolAutomaton.getStateFactory());

				IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;

				switch (mPref.interpolantAutomatonEnhancement()) {
				case NONE:
					final PowersetDeterminizer<CodeBlock, IPredicate> psd = new PowersetDeterminizer<CodeBlock, IPredicate>(
							interpolAutomaton, true, mPredicateFactoryInterpolantAutomata);
					if (mPref.differenceSenwa()) {
						diff = new DifferenceSenwa<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
								oldAbstraction, interpolAutomaton, psd, false);
					} else {
						diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
								oldAbstraction, interpolAutomaton, psd, mStateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
					}
					break;
				case BESTAPPROXIMATION_DEPRECATED:
					final BestApproximationDeterminizer bed = new BestApproximationDeterminizer(mSmtManager, mPref,
							interpolAutomaton, mPredicateFactoryInterpolantAutomata);
					diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
							oldAbstraction, interpolAutomaton, bed, mStateFactoryForRefinement,
							explointSigmaStarConcatOfIA);

					mLogger.info("Internal Transitions: " + bed.mAnswerInternalAutomaton
							+ " answers given by automaton " + bed.mAnswerInternalCache + " answers given by cache "
							+ bed.mAnswerInternalSolver + " answers given by solver");
					mLogger.info("Call Transitions: " + bed.mAnswerCallAutomaton + " answers given by automaton "
							+ bed.mAnswerCallCache + " answers given by cache " + bed.mAnswerCallSolver
							+ " answers given by solver");
					mLogger.info("Return Transitions: " + bed.mAnswerReturnAutomaton + " answers given by automaton "
							+ bed.mAnswerReturnCache + " answers given by cache " + bed.mAnswerReturnSolver
							+ " answers given by solver");
					break;
				case SELFLOOP:
					final SelfloopDeterminizer sed = new SelfloopDeterminizer(mSmtManager, mPref, interpolAutomaton,
							mPredicateFactoryInterpolantAutomata);
					if (mPref.differenceSenwa()) {
						diff = new DifferenceSenwa<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
								oldAbstraction, interpolAutomaton, sed, false);
					} else {
						diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
								oldAbstraction, interpolAutomaton, sed, mStateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
					}
					mLogger.info("Internal Selfloops: " + sed.mInternalSelfloop + " Internal NonSelfloops "
							+ sed.mInternalNonSelfloop);
					mLogger.info(
							"Call Selfloops: " + sed.mCallSelfloop + " Call NonSelfloops " + sed.mCallNonSelfloop);
					mLogger.info("Return Selfloops: " + sed.mReturnSelfloop + " Return NonSelfloops "
							+ sed.mReturnNonSelfloop);
					break;
				case PREDICATE_ABSTRACTION:
				case PREDICATE_ABSTRACTION_CONSERVATIVE:
				case PREDICATE_ABSTRACTION_CANNIBALIZE:
					if (mPref.differenceSenwa()) {
						throw new UnsupportedOperationException();
					} else {
						final boolean conservativeSuccessorCandidateSelection = (mPref
								.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE);
						final boolean cannibalize = (mPref
								.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE);
						final DeterministicInterpolantAutomaton determinized = new DeterministicInterpolantAutomaton(
								mServices, mSmtManager, mModGlobVarManager, htc, oldAbstraction, interpolAutomaton,
								mInterpolantGenerator.getPredicateUnifier(), mLogger,
								conservativeSuccessorCandidateSelection, cannibalize);
						// NondeterministicInterpolantAutomaton determinized =
						// new NondeterministicInterpolantAutomaton(
						// mServices, mSmtManager, mModGlobVarManager, htc,
						// oldAbstraction, interpolAutomaton,
						// mTraceChecker.getPredicateUnifier(), mLogger);
						// ComplementDeterministicNwa<CodeBlock, IPredicate>
						// cdnwa = new ComplementDeterministicNwa<>(dia);
						final PowersetDeterminizer<CodeBlock, IPredicate> psd2 = new PowersetDeterminizer<CodeBlock, IPredicate>(
								determinized, true, mPredicateFactoryInterpolantAutomata);

						diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
								oldAbstraction, determinized, psd2, mStateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
						determinized.switchToReadonlyMode();
						final INestedWordAutomaton<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(
								new AutomataLibraryServices(mServices), determinized)).getResult();
						if (mPref.dumpAutomata()) {
							final String filename = "EnhancedInterpolantAutomaton_Iteration" + mIteration;
							super.writeAutomatonToFile(test, filename);
						}
						if (mAbsIntRunner == null) {
							// check only if AI did not run
							final boolean ctxAccepted = (new Accepts<CodeBlock, IPredicate>(
									new AutomataLibraryServices(mServices), test,
									(NestedWord<CodeBlock>) mCounterexample.getWord(), true, false)).getResult();
							if (!ctxAccepted) {
								throw new AssertionError("enhanced interpolant automaton in iteration " + mIteration
										+ " broken: counterexample of length " + mCounterexample.getLength()
										+ " not accepted");
							}
						}
						assert (new InductivityCheck(mServices, test, false, true,
								new IncrementalHoareTripleChecker(mRootNode.getRootAnnot().getManagedScript(),
										mModGlobVarManager, mSmtManager.getBoogie2Smt()))).getResult();
					}
					break;
				case EAGER:
				case NO_SECOND_CHANCE:
				case EAGER_CONSERVATIVE: {
					final boolean conservativeSuccessorCandidateSelection = (mPref
							.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.EAGER_CONSERVATIVE);
					final boolean secondChance = (mPref
							.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE);
					final NondeterministicInterpolantAutomaton nondet = new NondeterministicInterpolantAutomaton(mServices,
							mSmtManager, mModGlobVarManager, htc,
							(INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction, interpolAutomaton,
							predicateUnifier, mLogger, conservativeSuccessorCandidateSelection, secondChance);
					final PowersetDeterminizer<CodeBlock, IPredicate> psd2 = new PowersetDeterminizer<CodeBlock, IPredicate>(
							nondet, true, mPredicateFactoryInterpolantAutomata);
					diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
							oldAbstraction, nondet, psd2, mStateFactoryForRefinement, explointSigmaStarConcatOfIA);
					nondet.switchToReadonlyMode();
					final INestedWordAutomaton<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(
							new AutomataLibraryServices(mServices), nondet)).getResult();
					if (mPref.dumpAutomata()) {
						final String filename = "EnhancedInterpolantAutomaton_Iteration" + mIteration;
						super.writeAutomatonToFile(test, filename);
					}
					final boolean ctxAccepted = (new Accepts<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
							test, (NestedWord<CodeBlock>) mCounterexample.getWord(), true, false)).getResult();
					if (!ctxAccepted) {
						throw new AssertionError("enhanced interpolant automaton in iteration " + mIteration
								+ " broken: counterexample of length " + mCounterexample.getLength()
								+ " not accepted");
					}
					assert (new InductivityCheck(mServices, test, false, true,
							new IncrementalHoareTripleChecker(mRootNode.getRootAnnot().getManagedScript(),
									mModGlobVarManager, mSmtManager.getBoogie2Smt()))).getResult();
				}
					break;
				default:
					throw new UnsupportedOperationException();
				}
				if (REMOVE_DEAD_ENDS) {
					if (mComputeHoareAnnotation) {
						final Difference<CodeBlock, IPredicate> difference = (Difference<CodeBlock, IPredicate>) diff;
						mHaf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
					}
					diff.removeDeadEnds();
					if (mComputeHoareAnnotation) {
						mHaf.addDeadEndDoubleDeckers(diff);
					}
				}

				mAbstraction = diff.getResult();
				// mDeadEndRemovalTime = diff.getDeadEndRemovalTime();

				if (mPref.dumpAutomata()) {
					final String filename = "InterpolantAutomaton_Iteration" + mIteration;
					super.writeAutomatonToFile(interpolAutomaton, filename);
				}
			} else {// complement and intersection instead of difference

				final INestedWordAutomatonOldApi<CodeBlock, IPredicate> dia = determinizeInterpolantAutomaton(
						interpolAutomaton);

				mLogger.debug("Start complementation");
				final INestedWordAutomatonOldApi<CodeBlock, IPredicate> nia = (new ComplementDD<CodeBlock, IPredicate>(
						new AutomataLibraryServices(mServices), mPredicateFactoryInterpolantAutomata, dia))
								.getResult();
				assert (!accepts(mServices, nia, mCounterexample.getWord()));
				mLogger.info("Complemented interpolant automaton has " + nia.size() + " states");

				if (mIteration <= mPref.watchIteration() && mPref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
					mArtifactAutomaton = nia;
				}
				assert (oldAbstraction.getStateFactory() == interpolAutomaton.getStateFactory());
				mLogger.debug("Start intersection");
				final IntersectDD<CodeBlock, IPredicate> intersect = new IntersectDD<CodeBlock, IPredicate>(
						new AutomataLibraryServices(mServices), false, oldAbstraction, nia);
				if (REMOVE_DEAD_ENDS && mComputeHoareAnnotation) {
					throw new AssertionError("not supported any more");
					// mHaf.wipeReplacedContexts();
					// mHaf.addDeadEndDoubleDeckers(intersect);
				}
				if (REMOVE_DEAD_ENDS) {
					intersect.removeDeadEnds();
				}
				mAbstraction = intersect.getResult();
			}
		} finally {
			mCegarLoopBenchmark.addEdgeCheckerData(htc.getEdgeCheckerBenchmark());
			mCegarLoopBenchmark.addPredicateUnifierData(predicateUnifier.getPredicateUnifierBenchmark());
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		}

		// if(mRemoveDeadEnds && mComputeHoareAnnotation) {
		// mHaf.wipeReplacedContexts();
		// mHaf.addDoubleDeckers(removedDoubleDeckers,
		// oldAbstraction.getEmptyStackState());
		// mHaf.addContext2Entry(context2entry);
		// }

		// (new RemoveDeadEnds<CodeBlock,
		// IPredicate>((INestedWordAutomatonOldApi<CodeBlock, IPredicate>)
		// mAbstraction)).getResult();
		mLogger.info(predicateUnifier.collectPredicateUnifierStatistics());

		final Minimization minimization = mPref.minimize();
		switch (minimization) {
		case NONE:
			break;
		case DFA_HOPCROFT_LISTS:
		case DFA_HOPCROFT_ARRAYS:
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
		case NWA_MAX_SAT:
		case NWA_COMBINATOR:
			minimizeAbstraction(mStateFactoryForRefinement, mPredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}

		// MinimizeSevpa<CodeBlock, Predicate> sev = new
		// MinimizeSevpa<CodeBlock, Predicate>(abstraction);
		// new MinimizeSevpa<CodeBlock, Predicate>.Partitioning(0);

		// for (Predicate p : a.getStates()) {
		// assert a.numberOfOutgoingInternalTransitions(p) <= 2 : p + " has "
		// +a.numberOfOutgoingInternalTransitions(p);
		// assert a.numberOfIncomingInternalTransitions(p) <= 25 : p + " has "
		// +a.numberOfIncomingInternalTransitions(p);
		// }
		final boolean stillAccepted = (new Accepts<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
				(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) mAbstraction,
				(NestedWord<CodeBlock>) mCounterexample.getWord())).getResult();
		if (stillAccepted) {
			return false;
		} else {
			return true;
		}
	}

	public static IHoareTripleChecker getEfficientHoareTripleChecker(IUltimateServiceProvider services,
			HoareTripleChecks hoareTripleChecks, SmtManager smtManager,
			ModifiableGlobalVariableManager modGlobVarManager, PredicateUnifier predicateUnifier)
			throws AssertionError {
		final IHoareTripleChecker solverHtc;
		switch (hoareTripleChecks) {
		case MONOLITHIC:
			solverHtc = new MonolithicHoareTripleChecker(smtManager.getManagedScript(), modGlobVarManager);
			break;
		case INCREMENTAL:
			solverHtc = new IncrementalHoareTripleChecker(smtManager.getManagedScript(), modGlobVarManager,
					smtManager.getBoogie2Smt());
			break;
		default:
			throw new AssertionError("unknown value");
		}
		final IHoareTripleChecker htc = new EfficientHoareTripleChecker(solverHtc, modGlobVarManager, predicateUnifier,
				smtManager);
		return htc;
	}

	/**
	 * Automata theoretic minimization of the automaton stored in mAbstraction. Expects that mAbstraction does not
	 * have dead ends.
	 * 
	 * @param predicateFactoryRefinement
	 *            PredicateFactory for the construction of the new (minimized) abstraction.
	 * @param resultCheckPredFac
	 *            PredicateFactory used for auxiliary automata used for checking correctness of the result (if
	 *            assertions are enabled).
	 */
	protected void minimizeAbstraction(PredicateFactoryForInterpolantAutomata predicateFactoryRefinement,
			PredicateFactoryResultChecking resultCheckPredFac, Minimization minimization)
			throws AutomataOperationCanceledException, AutomataLibraryException, AssertionError {
		if (mPref.dumpAutomata()) {
			final String filename = mRootNode.getFilename() + "_DiffAutomatonBeforeMinimization_Iteration" + mIteration;
			super.writeAutomatonToFile(mAbstraction, filename);
		}
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataMinimizationTime.toString());
		// long startTime = System.currentTimeMillis();
		final int oldSize = mAbstraction.size();
		final INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) mAbstraction;
		final Collection<Set<IPredicate>> partition = computePartition(newAbstraction);
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimized;
		try {
			switch (minimization) {
			case MINIMIZE_SEVPA: {
				final MinimizeSevpa<CodeBlock, IPredicate> minimizeOp = new MinimizeSevpa<CodeBlock, IPredicate>(
						new AutomataLibraryServices(mServices), newAbstraction, partition, predicateFactoryRefinement);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = minimizeOp.getResult();
				if (mComputeHoareAnnotation) {
					final Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					mHaf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case SHRINK_NWA: {
				final ShrinkNwa<CodeBlock, IPredicate> minimizeOp = new ShrinkNwa<CodeBlock, IPredicate>(
						new AutomataLibraryServices(mServices), predicateFactoryRefinement, newAbstraction, partition,
						true, false, false, 200, false, 0, false, false);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
						minimizeOp.getResult())).getResult();
				if (mComputeHoareAnnotation) {
					final Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					mHaf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case NWA_COMBINATOR: {
				final MinimizeNwaCombinator<CodeBlock, IPredicate> minimizeOp = new MinimizeNwaCombinator<CodeBlock, IPredicate>(
						new AutomataLibraryServices(mServices), predicateFactoryRefinement, newAbstraction, partition,
						mIteration);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
						minimizeOp.getResult())).getResult();
				if (mComputeHoareAnnotation && minimizeOp.supportHoareAnnotation()) {
					final Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					mHaf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case DFA_HOPCROFT_ARRAYS: {
				final MinimizeDfaHopcroftPaper<CodeBlock, IPredicate> minimizeOp = new MinimizeDfaHopcroftPaper<CodeBlock, IPredicate>(
						new AutomataLibraryServices(mServices), newAbstraction, predicateFactoryRefinement, partition,
						mComputeHoareAnnotation);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
						minimizeOp.getResult())).getResult();
				if (mComputeHoareAnnotation) {
					final Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					mHaf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case DFA_HOPCROFT_LISTS: {
				final MinimizeIncompleteDfa<CodeBlock, IPredicate> minimizeOp = new MinimizeIncompleteDfa<CodeBlock, IPredicate>(
						new AutomataLibraryServices(mServices), newAbstraction, predicateFactoryRefinement, partition,
						mComputeHoareAnnotation);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
						minimizeOp.getResult())).getResult();
				if (mComputeHoareAnnotation) {
					final Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					mHaf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case NWA_MAX_SAT: {
				final MinimizeNwaMaxSAT<CodeBlock, IPredicate> minimizeOp = new MinimizeNwaMaxSAT<CodeBlock, IPredicate>(
						new AutomataLibraryServices(mServices), predicateFactoryRefinement, newAbstraction);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
						minimizeOp.getResult())).getResult();
				if (mComputeHoareAnnotation) {
					throw new AssertionError("Hoare annotation and NWA_MAX_SAT incompatible");
				}
				break;
			}
			case NONE:
				minimized = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) mAbstraction;
				break;
			default:
				throw new AssertionError();
			}
			final int newSize = minimized.size();
			mAbstraction = minimized;
			if (oldSize != 0 && oldSize < newSize) {
				throw new AssertionError("Minimization increased state space");
			}
			mCegarLoopBenchmark.announceStatesRemovedByMinimization(oldSize - newSize);
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataMinimizationTime.toString());
		}
	}

	// private static Collection<Set<IPredicate>>
	// computePartitionDistinguishFinalNonFinal(
	// INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton, ILogger
	// logger) {
	// logger.info("Start computation of initial partition.");
	// Collection<IPredicate> states = automaton.getStates();
	// Map<ProgramPoint, Set<IPredicate>> pp2pFin = new HashMap<ProgramPoint,
	// Set<IPredicate>>();
	// Map<ProgramPoint, Set<IPredicate>> pp2pNonFin = new HashMap<ProgramPoint,
	// Set<IPredicate>>();
	// for (IPredicate p : states) {
	// ISLPredicate sp = (ISLPredicate) p;
	// if (automaton.isFinal(sp)) {
	// pigeonHole(pp2pFin, sp);
	// } else {
	// pigeonHole(pp2pNonFin, sp);
	// }
	//
	// }
	// Collection<Set<IPredicate>> partition = new ArrayList<Set<IPredicate>>();
	// for (ProgramPoint pp : pp2pFin.keySet()) {
	// Set<IPredicate> statesWithSamePP = pp2pFin.get(pp);
	// partition.add(statesWithSamePP);
	// }
	// for (ProgramPoint pp : pp2pNonFin.keySet()) {
	// Set<IPredicate> statesWithSamePP = pp2pNonFin.get(pp);
	// partition.add(statesWithSamePP);
	// }
	// logger.info("Finished computation of initial partition.");
	// return partition;
	// }

	protected Collection<Set<IPredicate>> computePartition(
			INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton) {
		mLogger.info("Start computation of initial partition.");
		final Collection<IPredicate> states = automaton.getStates();
		final Map<ProgramPoint, Set<IPredicate>> pp2p = new HashMap<ProgramPoint, Set<IPredicate>>();
		for (final IPredicate p : states) {
			final ISLPredicate sp = (ISLPredicate) p;
			pigeonHole(pp2p, sp);
		}
		final Collection<Set<IPredicate>> partition = new ArrayList<Set<IPredicate>>();
		for (final ProgramPoint pp : pp2p.keySet()) {
			final Set<IPredicate> statesWithSamePP = pp2p.get(pp);
			partition.add(statesWithSamePP);
		}
		mLogger.info("Finished computation of initial partition.");
		return partition;
	}

	/**
	 * Pigeon-hole (german: einsortieren) predicates according to their ProgramPoint
	 */
	private static void pigeonHole(Map<ProgramPoint, Set<IPredicate>> pp2p, ISLPredicate sp) {
		Set<IPredicate> statesWithSamePP = pp2p.get(sp.getProgramPoint());
		if (statesWithSamePP == null) {
			statesWithSamePP = new HashSet<IPredicate>();
			pp2p.put(sp.getProgramPoint(), statesWithSamePP);
		}
		statesWithSamePP.add(sp);
	}

	// private boolean eachStateIsFinal(Collection<IPredicate> states,
	// INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton) {
	// boolean result = true;
	// for (IPredicate p : states) {
	// result &= automaton.isFinal(p);
	// }
	// return result;
	// }

	protected INestedWordAutomatonOldApi<CodeBlock, IPredicate> determinizeInterpolantAutomaton(
			INestedWordAutomaton<CodeBlock, IPredicate> interpolAutomaton) throws AutomataOperationCanceledException {
		mLogger.debug("Start determinization");
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> dia;
		switch (mPref.interpolantAutomatonEnhancement()) {
		case NONE:
			final PowersetDeterminizer<CodeBlock, IPredicate> psd = new PowersetDeterminizer<CodeBlock, IPredicate>(
					interpolAutomaton, true, mPredicateFactoryInterpolantAutomata);
			final DeterminizeDD<CodeBlock, IPredicate> dabps = new DeterminizeDD<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), interpolAutomaton, psd);
			dia = dabps.getResult();
			break;
		case BESTAPPROXIMATION_DEPRECATED:
			final BestApproximationDeterminizer bed = new BestApproximationDeterminizer(mSmtManager, mPref,
					(NestedWordAutomaton<CodeBlock, IPredicate>) interpolAutomaton,
					mPredicateFactoryInterpolantAutomata);
			final DeterminizeDD<CodeBlock, IPredicate> dab = new DeterminizeDD<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), interpolAutomaton, bed);
			dia = dab.getResult();
			break;
		case SELFLOOP:
			final SelfloopDeterminizer sed = new SelfloopDeterminizer(mSmtManager, mPref, interpolAutomaton,
					mPredicateFactoryInterpolantAutomata);
			final DeterminizeDD<CodeBlock, IPredicate> dabsl = new DeterminizeDD<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices), interpolAutomaton, sed);
			dia = dabsl.getResult();
			break;
		default:
			throw new UnsupportedOperationException();
		}

		if (mComputeHoareAnnotation) {
			assert (new InductivityCheck(mServices, dia, false, true, new IncrementalHoareTripleChecker(
					mRootNode.getRootAnnot().getManagedScript(), mModGlobVarManager, mSmtManager.getBoogie2Smt())))
							.getResult() : "Not inductive";
		}
		if (mPref.dumpAutomata()) {
			final String filename = "InterpolantAutomatonDeterminized_Iteration" + mIteration;
			writeAutomatonToFile(dia, filename);
		}
		assert (accepts(mServices, dia, mCounterexample.getWord()));
		mLogger.debug("Sucessfully determinized");
		return dia;
	}

	@Override
	protected void computeCFGHoareAnnotation() {
		if (mSmtManager.isLocked()) {
			throw new AssertionError("SMTManager must not be locked at the beginning of Hoare annotation computation");
		}
		final INestedWordAutomatonOldApi<CodeBlock, IPredicate> abstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) mAbstraction;
		new HoareAnnotationExtractor(mServices, abstraction, mHaf);
		(new HoareAnnotationWriter(mRootNode.getRootAnnot(), mSmtManager, mHaf, mServices))
				.addHoareAnnotationToCFG();
	}

	@Override
	public IElement getArtifact() {
		if (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.INTERPOLANT_AUTOMATON
				|| mPref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {

			if (mArtifactAutomaton == null) {
				mLogger.warn("Preferred Artifact not available," + " visualizing the RCFG instead");
				return mRootNode;
			} else {
				try {
					return Automaton2UltimateModel.ultimateModel(new AutomataLibraryServices(mServices),
							mArtifactAutomaton);
				} catch (final AutomataOperationCanceledException e) {
					return null;
				}
			}
		} else if (mPref.artifact() == Artifact.RCFG) {
			return mRootNode;
		} else {
			throw new IllegalArgumentException();
		}
	}

	public void howDifferentAreInterpolants(Collection<IPredicate> predicates) {
		int implications = 0;
		int biimplications = 0;
		final IPredicate[] array = predicates.toArray(new IPredicate[0]);
		for (int i = 0; i < array.length; i++) {
			for (int j = 0; j < i; j++) {
				final boolean implies = (mSmtManager.isCovered(array[i], array[j]) == LBool.UNSAT);
				final boolean explies = (mSmtManager.isCovered(array[j], array[i]) == LBool.UNSAT);
				if (implies && explies) {
					biimplications++;
				} else if (implies ^ explies) {
					implications++;
				}

			}
		}
		mLogger.warn(
				array.length + "Interpolants. " + implications + " implications " + biimplications + " biimplications");
	}

	protected static boolean accepts(IUltimateServiceProvider services, INestedWordAutomaton<CodeBlock, IPredicate> nia,
			Word<CodeBlock> word) throws AutomataOperationCanceledException {
		try {
			return (new Accepts<CodeBlock, IPredicate>(new AutomataLibraryServices(services), nia,
					NestedWord.nestedWord(word), false, false)).getResult();
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}

	public CegarLoopStatisticsGenerator getCegarLoopBenchmark() {
		return mCegarLoopBenchmark;
	}

	/**
	 * method called at the end of the cegar loop
	 */
	public void finish() {
		// do nothing
	}

	public void setWitnessAutomaton(NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		mWitnessAutomaton = witnessAutomaton;

	}

}
