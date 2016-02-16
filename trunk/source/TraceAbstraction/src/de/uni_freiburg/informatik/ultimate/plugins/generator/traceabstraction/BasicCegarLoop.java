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
import de.uni_freiburg.informatik.ultimate.automata.Automaton2UltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizeDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IntersectDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
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
	protected final static boolean TRACE_HISTOGRAMM_BAILOUT = false;

	protected HoareAnnotationFragments m_Haf;

	protected final PredicateFactoryRefinement m_StateFactoryForRefinement;
	protected final PredicateFactory m_PredicateFactoryInterpolantAutomata;
	protected final PredicateFactoryResultChecking m_PredicateFactoryResultChecking;

	protected boolean m_FallbackToFpIfInterprocedural = true;
	protected final INTERPOLATION m_Interpolation;
	protected final InterpolantAutomaton m_InterpolantAutomatonConstructionProcedure;
	protected final UnsatCores m_UnsatCores;
	protected final boolean m_UseLiveVariables;

	protected final boolean m_ComputeHoareAnnotation;

	private final boolean m_UseInterpolantConsolidation;

	protected final AssertCodeBlockOrder m_AssertCodeBlocksIncrementally;

	protected final boolean mAbsIntMode;
	private Map<IPredicate, Term> mAbsIntLoc2Term;
	private NestedWordAutomaton<WitnessEdge, WitnessNode> m_WitnessAutomaton;
	// private IHoareTripleChecker m_HoareTripleChecker;
	private boolean m_DoFaultLocalization = false;

	public BasicCegarLoop(String name, RootNode rootNode, SmtManager smtManager, TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs, INTERPOLATION interpolation, boolean computeHoareAnnotation,
			IUltimateServiceProvider services, IToolchainStorage storage) {

		super(services, storage, name, rootNode, smtManager, taPrefs, errorLocs,
				services.getLoggingService().getLogger(Activator.s_PLUGIN_ID));
		mAbsIntMode = new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_USE_ABSTRACT_INTERPRETATION);
		m_UseInterpolantConsolidation = new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
				.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLANTS_CONSOLIDATION);
		if (m_FallbackToFpIfInterprocedural && rootNode.getRootAnnot().getEntryNodes().size() > 1) {
			if (interpolation == INTERPOLATION.FPandBP) {
				mLogger.info("fallback from FPandBP to FP because CFG is interprocedural");
				m_Interpolation = INTERPOLATION.ForwardPredicates;
			} else {
				m_Interpolation = interpolation;
			}
			if (m_Pref.interpolantAutomaton() == InterpolantAutomaton.TWOTRACK) {
				m_InterpolantAutomatonConstructionProcedure = InterpolantAutomaton.CANONICAL;
			} else {
				m_InterpolantAutomatonConstructionProcedure = m_Pref.interpolantAutomaton();
			}
		} else {
			m_Interpolation = interpolation;
			m_InterpolantAutomatonConstructionProcedure = m_Pref.interpolantAutomaton();
		}
		// InterpolationPreferenceChecker.check(Activator.s_PLUGIN_NAME, interpolation);
		m_ComputeHoareAnnotation = computeHoareAnnotation;
		m_Haf = new HoareAnnotationFragments(mLogger);
		m_StateFactoryForRefinement = new PredicateFactoryRefinement(m_RootNode.getRootAnnot().getProgramPoints(),
				super.m_SmtManager, m_Pref, REMOVE_DEAD_ENDS && m_ComputeHoareAnnotation, m_Haf);
		m_PredicateFactoryInterpolantAutomata = new PredicateFactory(super.m_SmtManager, m_Pref);

		m_AssertCodeBlocksIncrementally = (new UltimatePreferenceStore(Activator.s_PLUGIN_ID)).getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY,
				AssertCodeBlockOrder.class);

		m_PredicateFactoryResultChecking = new PredicateFactoryResultChecking(smtManager);
		m_CegarLoopBenchmark = new CegarLoopBenchmarkGenerator();
		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_OverallTime);

		UltimatePreferenceStore m_Prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		m_UnsatCores = m_Prefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_UNSAT_CORES, UnsatCores.class);
		m_UseLiveVariables = m_Prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_LIVE_VARIABLES);
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		CFG2NestedWordAutomaton cFG2NestedWordAutomaton = new CFG2NestedWordAutomaton(m_Services,
				m_Pref.interprocedural(), super.m_SmtManager, mLogger);

		m_Abstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(super.m_RootNode, m_StateFactoryForRefinement,
				super.m_ErrorLocs);
		if (m_WitnessAutomaton != null) {
			WitnessProductAutomaton wpa = new WitnessProductAutomaton(m_Services,
					(INestedWordAutomatonSimple<CodeBlock, IPredicate>) m_Abstraction, m_WitnessAutomaton,
					m_SmtManager);
			INestedWordAutomatonSimple<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(
					new AutomataLibraryServices(m_Services), wpa)).getResult();
			mLogger.info("Full witness product has " + test.sizeInformation());
			mLogger.info(wpa.generateBadWitnessInformation());
			final LineCoverageCalculator origCoverage = new LineCoverageCalculator(m_Services, m_Abstraction);
			m_Abstraction = (new RemoveDeadEnds<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), wpa))
					.getResult();
			new LineCoverageCalculator(m_Services, m_Abstraction, origCoverage).reportCoverage("Witness product");
		}
	}

	@Override
	protected boolean isAbstractionCorrect() throws OperationCanceledException {
		final INestedWordAutomatonOldApi<CodeBlock, IPredicate> abstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		try {
			m_Counterexample = (new IsEmpty<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
					abstraction)).getNestedRun();
		} catch (OperationCanceledException e) {
			e.printStackTrace();
		}

		if (m_Counterexample == null) {
			return true;
		}

		if (mAbsIntMode) {
			m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AbsIntTime);
			mAbsIntLoc2Term = null;

			// allow for 20% of the remaining time
			final IProgressAwareTimer timer = m_Services.getProgressMonitorService().getChildTimer(0.2);
			mLogger.info("Running abstract interpretation on error trace of length " + m_Counterexample.getLength());
			final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, IPredicate> result = AbstractInterpreter
					.runSilently((NestedRun<CodeBlock, IPredicate>) m_Counterexample, abstraction, m_RootNode, timer,
							m_Services);
			mAbsIntLoc2Term = result.getTerms();
			assert mAbsIntLoc2Term != null : "Abstract interpretation did return an invalid term map";
			m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AbsIntTime);
		}

		if (m_Pref.dumpAutomata()) {
			dumpNestedRun(m_Counterexample, m_IterationPW, mLogger);
		}
		// m_RunAnalyzer = new RunAnalyzer(m_Counterexample);
		mLogger.info("Found error trace");
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(m_Counterexample.getWord());
		}
		HistogramOfIterable<CodeBlock> traceHistogram = new HistogramOfIterable<CodeBlock>(m_Counterexample.getWord());
		if (mLogger.isInfoEnabled()) {
			mLogger.info("trace histogram " + traceHistogram.toString());
		}
		if (TRACE_HISTOGRAMM_BAILOUT) {
			if (traceHistogram.getVisualizationArray()[0] > traceHistogram.getVisualizationArray().length) {
				throw new ToolchainCanceledException(getClass(),
						"bailout by trace histogram " + traceHistogram.toString());
			}
		}
		// s_Logger.info("Cutpoints: " + m_RunAnalyzer.getCutpoints());
		// s_Logger.debug(m_RunAnalyzer.getOccurence());
		return false;
	}

	@Override
	protected LBool isCounterexampleFeasible() {
		PredicateUnifier predicateUnifier = new PredicateUnifier(m_Services, m_SmtManager);
		IPredicate truePredicate = predicateUnifier.getTruePredicate();
		IPredicate falsePredicate = predicateUnifier.getFalsePredicate();

		InterpolatingTraceChecker interpolatingTraceChecker = null;
		final SmtManager smtMangerTracechecks;
		if (m_Pref.useSeparateSolverForTracechecks()) {
			Script tcSolver = SolverBuilder.buildAndInitializeSolver(m_Services, m_ToolchainStorage,
					m_RootNode.getFilename() + "_TraceCheck_Iteration" + m_Iteration, m_Pref.solverMode(),
					m_Pref.dumpSmtScriptToFile(), m_Pref.pathOfDumpedScript(), m_Pref.commandExternalSolver(), false,
					false, m_Pref.logicForExternalSolver(), "TraceCheck_Iteration" + m_Iteration);
			smtMangerTracechecks = new SmtManager(tcSolver, m_RootNode.getRootAnnot().getBoogie2SMT(),
					m_RootNode.getRootAnnot().getModGlobVarManager(), m_Services, false);
			TermTransferrer tt = new TermTransferrer(tcSolver);
			for (Term axiom : m_RootNode.getRootAnnot().getBoogie2SMT().getAxioms()) {
				tcSolver.assertTerm(tt.transform(axiom));
			}
		} else {
			smtMangerTracechecks = m_SmtManager;
		}

		final LBool feasibility;
		switch (m_Interpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation: {
			interpolatingTraceChecker = new InterpolatingTraceCheckerCraig(truePredicate, falsePredicate,
					new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(m_Counterexample.getWord()), m_SmtManager,
					m_RootNode.getRootAnnot().getModGlobVarManager(), m_AssertCodeBlocksIncrementally, m_Services, true,
					predicateUnifier, m_Interpolation, smtMangerTracechecks, true);
		}
			break;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
			interpolatingTraceChecker = new TraceCheckerSpWp(truePredicate, falsePredicate,
					new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(m_Counterexample.getWord()), m_SmtManager,
					m_RootNode.getRootAnnot().getModGlobVarManager(), m_AssertCodeBlocksIncrementally, m_UnsatCores,
					m_UseLiveVariables, m_Services, true, predicateUnifier, m_Interpolation, smtMangerTracechecks);

			break;
		case PathInvariants:
			interpolatingTraceChecker = new InterpolatingTraceCheckerPathInvariantsWithFallback(truePredicate,
					falsePredicate, new TreeMap<Integer, IPredicate>(),
					(NestedRun<CodeBlock, IPredicate>) m_Counterexample, m_SmtManager, m_ModGlobVarManager,
					m_AssertCodeBlocksIncrementally, m_Services, m_ToolchainStorage, true, predicateUnifier);
			break;
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		m_CegarLoopBenchmark.addTraceCheckerData(interpolatingTraceChecker.getTraceCheckerBenchmark());
		if (interpolatingTraceChecker.getToolchainCancelledExpection() != null) {
			throw interpolatingTraceChecker.getToolchainCancelledExpection();
		} else {
			if (m_Pref.useSeparateSolverForTracechecks()) {
				smtMangerTracechecks.getScript().exit();
			}
		}

		feasibility = interpolatingTraceChecker.isCorrect();
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample might be feasible");
			NestedWord<CodeBlock> counterexample = NestedWord.nestedWord(m_Counterexample.getWord());
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
			if (m_DoFaultLocalization && feasibility == LBool.SAT) {
				new FlowSensitiveFaultLocalizer(m_Counterexample,
						(INestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction, m_Services, m_SmtManager,
						m_ModGlobVarManager, predicateUnifier);
			}
			// s_Logger.info("Trace with values");
			// s_Logger.info(interpolatingTraceChecker.getRcfgProgramExecution());
			m_RcfgProgramExecution = interpolatingTraceChecker.getRcfgProgramExecution();
		}
		m_CegarLoopBenchmark.addTraceCheckerData(interpolatingTraceChecker.getTraceCheckerBenchmark());
		// m_TraceCheckerBenchmark.aggregateBenchmarkData(interpolatingTraceChecker.getTraceCheckerBenchmark());
		m_InterpolantGenerator = interpolatingTraceChecker;
		if (m_UseInterpolantConsolidation) {
			try {
				InterpolantConsolidation interpConsoli = new InterpolantConsolidation(truePredicate, falsePredicate,
						new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(m_Counterexample.getWord()),
						m_SmtManager, m_RootNode.getRootAnnot().getModGlobVarManager(), m_Services, mLogger,
						predicateUnifier, interpolatingTraceChecker, m_Pref);
				// Add benchmark data of interpolant consolidation
				m_CegarLoopBenchmark
						.addInterpolationConsolidationData(interpConsoli.getInterpolantConsolidationBenchmarks());
				m_InterpolantGenerator = interpConsoli;
			} catch (OperationCanceledException e) {
				// Timeout
				e.printStackTrace();
			}
		}
		return feasibility;
	}

	@Override
	protected void constructInterpolantAutomaton() throws OperationCanceledException {
		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime);
		switch (m_InterpolantAutomatonConstructionProcedure) {
		case CANONICAL: {
			List<ProgramPoint> programPoints = CoverageAnalysis.extractProgramPoints(m_Counterexample);
			CanonicalInterpolantAutomatonBuilder iab = new CanonicalInterpolantAutomatonBuilder(m_Services,
					m_InterpolantGenerator, programPoints, new InCaReAlphabet<CodeBlock>(m_Abstraction), m_SmtManager,
					m_PredicateFactoryInterpolantAutomata, mLogger);
			iab.analyze();
			m_InterpolAutomaton = iab.getInterpolantAutomaton();
			mLogger.info("Interpolants " + m_InterpolAutomaton.getStates());

			// m_CegarLoopBenchmark.addBackwardCoveringInformation(iab.getBackwardCoveringInformation());
			BackwardCoveringInformation bci = TraceCheckerUtils.computeCoverageCapability(m_Services,
					m_InterpolantGenerator, programPoints, mLogger);
			m_CegarLoopBenchmark.addBackwardCoveringInformation(bci);
		}
			break;
		case SINGLETRACE: {
			StraightLineInterpolantAutomatonBuilder iab = new StraightLineInterpolantAutomatonBuilder(m_Services,
					new InCaReAlphabet<CodeBlock>(m_Abstraction), m_InterpolantGenerator,
					m_PredicateFactoryInterpolantAutomata);
			m_InterpolAutomaton = iab.getResult();
		}
			break;
		case TOTALINTERPOLATION:
			throw new AssertionError("not supported by this CegarLoop");
		case TWOTRACK: {
			if (!(m_InterpolantGenerator instanceof TraceCheckerSpWp)
					&& !(m_InterpolantGenerator instanceof InterpolantConsolidation)) {
				throw new AssertionError("TWOTRACK only for TraceCheckerSpWp or InterpolantConsolidation");
			}
			IPredicate[] predicatesA = null;
			IPredicate[] predicatesB = null;
			boolean build2TrackAutomaton = false;
			if (m_InterpolantGenerator instanceof TraceCheckerSpWp) {
				TraceCheckerSpWp traceChecker = (TraceCheckerSpWp) m_InterpolantGenerator;
				predicatesA = traceChecker.getForwardPredicates();
				predicatesB = traceChecker.getBackwardPredicates();
				build2TrackAutomaton = true;
			} else if (!((InterpolantConsolidation) m_InterpolantGenerator).consolidationSuccessful()) {
				// if consolidation wasn't successful, then build a 2-Track-Automaton
				InterpolantConsolidation ic = (InterpolantConsolidation) m_InterpolantGenerator;
				predicatesA = ic.getInterpolantsOfType_I();
				predicatesB = ic.getInterpolantsOfType_II();
				build2TrackAutomaton = true;
			}
			if (build2TrackAutomaton) {
				TwoTrackInterpolantAutomatonBuilder ttiab = new TwoTrackInterpolantAutomatonBuilder(m_Services,
						m_Counterexample, m_SmtManager, predicatesA, predicatesB,
						m_InterpolantGenerator.getPrecondition(), m_InterpolantGenerator.getPostcondition(),
						m_Abstraction);
				m_InterpolAutomaton = ttiab.getResult();
			} else {
				// Case of Canonical_Automaton, i.e. if the consolidation was successful
				// FIXME: The case TWOTRACK from the switch is not nice. Should be refactored!
				List<ProgramPoint> programPoints = CoverageAnalysis.extractProgramPoints(m_Counterexample);
				CanonicalInterpolantAutomatonBuilder iab = new CanonicalInterpolantAutomatonBuilder(m_Services,
						m_InterpolantGenerator, programPoints, new InCaReAlphabet<CodeBlock>(m_Abstraction),
						m_SmtManager, m_PredicateFactoryInterpolantAutomata, mLogger);
				iab.analyze();
				m_InterpolAutomaton = iab.getInterpolantAutomaton();
				mLogger.info("Interpolants " + m_InterpolAutomaton.getStates());

				// m_CegarLoopBenchmark.addBackwardCoveringInformation(iab.getBackwardCoveringInformation());
				BackwardCoveringInformation bci = TraceCheckerUtils.computeCoverageCapability(m_Services,
						m_InterpolantGenerator, programPoints, mLogger);
				m_CegarLoopBenchmark.addBackwardCoveringInformation(bci);
			}
			break;
		}
		case TOTALINTERPOLATION2: {
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction = (INestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction;
			NestedRun<CodeBlock, IPredicate> counterexample = (NestedRun<CodeBlock, IPredicate>) m_Counterexample;
			TotalInterpolationAutomatonBuilder iab = new TotalInterpolationAutomatonBuilder(abstraction,
					counterexample.getStateSequence(), m_InterpolantGenerator, m_SmtManager,
					m_PredicateFactoryInterpolantAutomata, m_RootNode.getRootAnnot().getModGlobVarManager(),
					m_Interpolation, m_Services, m_Pref.getHoareTripleChecks());
			m_InterpolAutomaton = iab.getResult();
			m_CegarLoopBenchmark.addTotalInterpolationData(iab.getTotalInterpolationBenchmark());
		}
			break;
		}
		m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime);
		assert (accepts(m_Services, m_InterpolAutomaton, m_Counterexample.getWord())) : "Interpolant automaton broken!";
		assert (new InductivityCheck(m_Services, m_InterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(m_SmtManager, m_ModGlobVarManager))).getResult();
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		final NestedWordAutomaton<CodeBlock, IPredicate> interpolAutomaton = m_InterpolAutomaton;
		final PredicateUnifier predUnifier = m_InterpolantGenerator.getPredicateUnifier();
		if (mAbsIntMode) {
			m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AbsIntTime);

			final NestedWordAutomaton<CodeBlock, IPredicate> aiInterpolAutomaton = new AbstractInterpretationAutomatonGenerator(
					m_Services, (INestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction, mAbsIntLoc2Term,
					predUnifier, m_SmtManager).getResult();
			refineWithGivenAutomaton(aiInterpolAutomaton, predUnifier);
			m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AbsIntTime);
			mLogger.info("Finished refinement with abstract interpretation automaton");
		}
		return refineWithGivenAutomaton(interpolAutomaton, predUnifier);

	}

	private boolean refineWithGivenAutomaton(NestedWordAutomaton<CodeBlock, IPredicate> interpolAutomaton,
			PredicateUnifier predicateUnifier)
					throws AssertionError, OperationCanceledException, AutomataLibraryException {
		m_StateFactoryForRefinement.setIteration(super.m_Iteration);
		// howDifferentAreInterpolants(interpolAutomaton.getStates());

		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AutomataDifference);
		boolean explointSigmaStarConcatOfIA = !m_ComputeHoareAnnotation;

		INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldAbstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		// Map<IPredicate, Set<IPredicate>> removedDoubleDeckers = null;
		// Map<IPredicate, IPredicate> context2entry = null;

		final CachingHoareTripleChecker htc;
		if (m_InterpolantGenerator instanceof InterpolantConsolidation) {
			htc = ((InterpolantConsolidation) m_InterpolantGenerator).getHoareTripleChecker();
		} else {
			IHoareTripleChecker ehtc = getEfficientHoareTripleChecker(m_Pref.getHoareTripleChecks(), m_SmtManager,
					m_ModGlobVarManager, m_InterpolantGenerator.getPredicateUnifier());
			htc = new CachingHoareTripleChecker(ehtc, m_InterpolantGenerator.getPredicateUnifier());
		}
		try {
			if (DIFFERENCE_INSTEAD_OF_INTERSECTION) {
				mLogger.debug("Start constructing difference");
				// assert(oldAbstraction.getStateFactory() ==
				// interpolAutomaton.getStateFactory());

				IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;

				switch (m_Pref.interpolantAutomatonEnhancement()) {
				case NONE:
					PowersetDeterminizer<CodeBlock, IPredicate> psd = new PowersetDeterminizer<CodeBlock, IPredicate>(
							interpolAutomaton, true, m_PredicateFactoryInterpolantAutomata);
					if (m_Pref.differenceSenwa()) {
						diff = new DifferenceSenwa<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
								oldAbstraction, interpolAutomaton, psd, false);
					} else {
						diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
								oldAbstraction, interpolAutomaton, psd, m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
					}
					break;
				case BESTAPPROXIMATION_DEPRECATED:
					BestApproximationDeterminizer bed = new BestApproximationDeterminizer(m_SmtManager, m_Pref,
							interpolAutomaton, m_PredicateFactoryInterpolantAutomata);
					diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
							oldAbstraction, interpolAutomaton, bed, m_StateFactoryForRefinement,
							explointSigmaStarConcatOfIA);

					mLogger.info("Internal Transitions: " + bed.m_AnswerInternalAutomaton
							+ " answers given by automaton " + bed.m_AnswerInternalCache + " answers given by cache "
							+ bed.m_AnswerInternalSolver + " answers given by solver");
					mLogger.info("Call Transitions: " + bed.m_AnswerCallAutomaton + " answers given by automaton "
							+ bed.m_AnswerCallCache + " answers given by cache " + bed.m_AnswerCallSolver
							+ " answers given by solver");
					mLogger.info("Return Transitions: " + bed.m_AnswerReturnAutomaton + " answers given by automaton "
							+ bed.m_AnswerReturnCache + " answers given by cache " + bed.m_AnswerReturnSolver
							+ " answers given by solver");
					break;
				case SELFLOOP:
					SelfloopDeterminizer sed = new SelfloopDeterminizer(m_SmtManager, m_Pref, interpolAutomaton,
							m_PredicateFactoryInterpolantAutomata);
					if (m_Pref.differenceSenwa()) {
						diff = new DifferenceSenwa<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
								oldAbstraction, interpolAutomaton, sed, false);
					} else {
						diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
								oldAbstraction, interpolAutomaton, sed, m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
					}
					mLogger.info("Internal Selfloops: " + sed.m_InternalSelfloop + " Internal NonSelfloops "
							+ sed.m_InternalNonSelfloop);
					mLogger.info(
							"Call Selfloops: " + sed.m_CallSelfloop + " Call NonSelfloops " + sed.m_CallNonSelfloop);
					mLogger.info("Return Selfloops: " + sed.m_ReturnSelfloop + " Return NonSelfloops "
							+ sed.m_ReturnNonSelfloop);
					break;
				case PREDICATE_ABSTRACTION:
				case PREDICATE_ABSTRACTION_CONSERVATIVE:
				case PREDICATE_ABSTRACTION_CANNIBALIZE:
					if (m_Pref.differenceSenwa()) {
						throw new UnsupportedOperationException();
					} else {
						boolean conservativeSuccessorCandidateSelection = (m_Pref
								.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE);
						boolean cannibalize = (m_Pref
								.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE);
						DeterministicInterpolantAutomaton determinized = new DeterministicInterpolantAutomaton(
								m_Services, m_SmtManager, m_ModGlobVarManager, htc, oldAbstraction, interpolAutomaton,
								m_InterpolantGenerator.getPredicateUnifier(), mLogger,
								conservativeSuccessorCandidateSelection, cannibalize);
						// NondeterministicInterpolantAutomaton determinized =
						// new NondeterministicInterpolantAutomaton(
						// m_Services, m_SmtManager, m_ModGlobVarManager, htc,
						// oldAbstraction, interpolAutomaton,
						// m_TraceChecker.getPredicateUnifier(), mLogger);
						// ComplementDeterministicNwa<CodeBlock, IPredicate>
						// cdnwa = new ComplementDeterministicNwa<>(dia);
						PowersetDeterminizer<CodeBlock, IPredicate> psd2 = new PowersetDeterminizer<CodeBlock, IPredicate>(
								determinized, true, m_PredicateFactoryInterpolantAutomata);

						diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
								oldAbstraction, determinized, psd2, m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
						determinized.switchToReadonlyMode();
						INestedWordAutomaton<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(
								new AutomataLibraryServices(m_Services), determinized)).getResult();
						if (m_Pref.dumpAutomata()) {
							String filename = "EnhancedInterpolantAutomaton_Iteration" + m_Iteration;
							super.writeAutomatonToFile(test, filename);
						}
						boolean ctxAccepted = (new Accepts<CodeBlock, IPredicate>(
								new AutomataLibraryServices(m_Services), test,
								(NestedWord<CodeBlock>) m_Counterexample.getWord(), true, false)).getResult();
						if (!ctxAccepted) {
							if (!mAbsIntMode) {
								throw new AssertionError("enhanced interpolant automaton in iteration " + m_Iteration
										+ " broken: counterexample of length " + m_Counterexample.getLength()
										+ " not accepted");
							} else {
								mLogger.warn("Enhanced interpolant automaton in iteration " + m_Iteration
										+ " did not accept counterexample of length " + m_Counterexample.getLength()
										+ " during abstract interpretation mode");
							}
						}
						assert (new InductivityCheck(m_Services, test, false, true,
								new IncrementalHoareTripleChecker(m_SmtManager, m_ModGlobVarManager))).getResult();
					}
					break;
				case EAGER:
				case NO_SECOND_CHANCE:
				case EAGER_CONSERVATIVE: {
					boolean conservativeSuccessorCandidateSelection = (m_Pref
							.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.EAGER_CONSERVATIVE);
					boolean secondChance = (m_Pref
							.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE);
					NondeterministicInterpolantAutomaton nondet = new NondeterministicInterpolantAutomaton(m_Services,
							m_SmtManager, m_ModGlobVarManager, htc,
							(INestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction, interpolAutomaton,
							predicateUnifier, mLogger, conservativeSuccessorCandidateSelection, secondChance);
					PowersetDeterminizer<CodeBlock, IPredicate> psd2 = new PowersetDeterminizer<CodeBlock, IPredicate>(
							nondet, true, m_PredicateFactoryInterpolantAutomata);
					diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
							oldAbstraction, nondet, psd2, m_StateFactoryForRefinement, explointSigmaStarConcatOfIA);
					nondet.switchToReadonlyMode();
					INestedWordAutomaton<CodeBlock, IPredicate> test = (new RemoveUnreachable<CodeBlock, IPredicate>(
							new AutomataLibraryServices(m_Services), nondet)).getResult();
					if (m_Pref.dumpAutomata()) {
						String filename = "EnhancedInterpolantAutomaton_Iteration" + m_Iteration;
						super.writeAutomatonToFile(test, filename);
					}
					boolean ctxAccepted = (new Accepts<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
							test, (NestedWord<CodeBlock>) m_Counterexample.getWord(), true, false)).getResult();
					if (!ctxAccepted) {
						throw new AssertionError("enhanced interpolant automaton in iteration " + m_Iteration
								+ " broken: counterexample of length " + m_Counterexample.getLength()
								+ " not accepted");
					}
					assert (new InductivityCheck(m_Services, test, false, true,
							new IncrementalHoareTripleChecker(m_SmtManager, m_ModGlobVarManager))).getResult();
				}
					break;
				default:
					throw new UnsupportedOperationException();
				}
				if (REMOVE_DEAD_ENDS) {
					if (m_ComputeHoareAnnotation) {
						Difference<CodeBlock, IPredicate> difference = (Difference<CodeBlock, IPredicate>) diff;
						m_Haf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
					}
					diff.removeDeadEnds();
					if (m_ComputeHoareAnnotation) {
						m_Haf.addDeadEndDoubleDeckers(diff);
					}
				}

				m_Abstraction = (IAutomaton<CodeBlock, IPredicate>) diff.getResult();
				// m_DeadEndRemovalTime = diff.getDeadEndRemovalTime();
				if (m_Pref.dumpAutomata()) {
					String filename = "InterpolantAutomaton_Iteration" + m_Iteration;
					super.writeAutomatonToFile(interpolAutomaton, filename);
				}
			} else {// complement and intersection instead of difference

				INestedWordAutomatonOldApi<CodeBlock, IPredicate> dia = determinizeInterpolantAutomaton(
						interpolAutomaton);

				mLogger.debug("Start complementation");
				INestedWordAutomatonOldApi<CodeBlock, IPredicate> nia = (new ComplementDD<CodeBlock, IPredicate>(
						new AutomataLibraryServices(m_Services), m_PredicateFactoryInterpolantAutomata, dia))
								.getResult();
				assert (!accepts(m_Services, nia, m_Counterexample.getWord()));
				mLogger.info("Complemented interpolant automaton has " + nia.size() + " states");

				if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
					m_ArtifactAutomaton = nia;
				}
				assert (oldAbstraction.getStateFactory() == interpolAutomaton.getStateFactory());
				mLogger.debug("Start intersection");
				IntersectDD<CodeBlock, IPredicate> intersect = new IntersectDD<CodeBlock, IPredicate>(
						new AutomataLibraryServices(m_Services), false, oldAbstraction, nia);
				if (REMOVE_DEAD_ENDS && m_ComputeHoareAnnotation) {
					throw new AssertionError("not supported any more");
					// m_Haf.wipeReplacedContexts();
					// m_Haf.addDeadEndDoubleDeckers(intersect);
				}
				if (REMOVE_DEAD_ENDS) {
					intersect.removeDeadEnds();
				}
				m_Abstraction = intersect.getResult();
			}
		} finally {
			m_CegarLoopBenchmark.addEdgeCheckerData(htc.getEdgeCheckerBenchmark());
			m_CegarLoopBenchmark.addPredicateUnifierData(predicateUnifier.getPredicateUnifierBenchmark());
			m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AutomataDifference);
		}

		// if(m_RemoveDeadEnds && m_ComputeHoareAnnotation) {
		// m_Haf.wipeReplacedContexts();
		// m_Haf.addDoubleDeckers(removedDoubleDeckers,
		// oldAbstraction.getEmptyStackState());
		// m_Haf.addContext2Entry(context2entry);
		// }

		// (new RemoveDeadEnds<CodeBlock,
		// IPredicate>((INestedWordAutomatonOldApi<CodeBlock, IPredicate>)
		// m_Abstraction)).getResult();
		mLogger.info(predicateUnifier.collectPredicateUnifierStatistics());

		Minimization minimization = m_Pref.minimize();
		switch (minimization) {
		case NONE:
			break;
		case DFA_HOPCROFT_LISTS:
		case DFA_HOPCROFT_ARRAYS:
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
			minimizeAbstraction(m_StateFactoryForRefinement, m_PredicateFactoryResultChecking, minimization);
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
		boolean stillAccepted = (new Accepts<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
				(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction,
				(NestedWord<CodeBlock>) m_Counterexample.getWord())).getResult();
		if (stillAccepted) {
			return false;
		} else {
			return true;
		}
	}

	public static IHoareTripleChecker getEfficientHoareTripleChecker(HoareTripleChecks hoareTripleChecks,
			SmtManager smtManager, ModifiableGlobalVariableManager modGlobVarManager, PredicateUnifier predicateUnifier)
					throws AssertionError {
		final IHoareTripleChecker solverHtc;
		switch (hoareTripleChecks) {
		case MONOLITHIC:
			solverHtc = new MonolithicHoareTripleChecker(smtManager);
			break;
		case INCREMENTAL:
			solverHtc = new IncrementalHoareTripleChecker(smtManager, modGlobVarManager);
			break;
		default:
			throw new AssertionError("unknown value");
		}
		IHoareTripleChecker htc = new EfficientHoareTripleChecker(solverHtc, modGlobVarManager, predicateUnifier,
				smtManager);
		return htc;
	}

	/**
	 * Automata theoretic minimization of the automaton stored in m_Abstraction. Expects that m_Abstraction does not
	 * have dead ends.
	 * 
	 * @param predicateFactoryRefinement
	 *            PredicateFactory for the construction of the new (minimized) abstraction.
	 * @param resultCheckPredFac
	 *            PredicateFactory used for auxiliary automata used for checking correctness of the result (if
	 *            assertions are enabled).
	 */
	protected void minimizeAbstraction(PredicateFactory predicateFactoryRefinement,
			PredicateFactoryResultChecking resultCheckPredFac, Minimization minimization)
					throws OperationCanceledException, AutomataLibraryException, AssertionError {
		if (m_Pref.dumpAutomata()) {
			String filename = "AbstractionBeforeMinimization_Iteration" + m_Iteration;
			super.writeAutomatonToFile(m_Abstraction, filename);
		}
		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AutomataMinimizationTime);
		// long startTime = System.currentTimeMillis();
		int oldSize = m_Abstraction.size();
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		Collection<Set<IPredicate>> partition = computePartition(newAbstraction);
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimized;
		try {
			switch (minimization) {
			case MINIMIZE_SEVPA: {
				MinimizeSevpa<CodeBlock, IPredicate> minimizeOp = new MinimizeSevpa<CodeBlock, IPredicate>(
						new AutomataLibraryServices(m_Services), newAbstraction, partition, predicateFactoryRefinement);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = minimizeOp.getResult();
				if (m_ComputeHoareAnnotation) {
					Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					m_Haf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case SHRINK_NWA: {
				ShrinkNwa<CodeBlock, IPredicate> minimizeOp = new ShrinkNwa<CodeBlock, IPredicate>(
						new AutomataLibraryServices(m_Services), predicateFactoryRefinement, newAbstraction, partition,
						true, false, false, 200, false, 0, false, false);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
						minimizeOp.getResult())).getResult();
				if (m_ComputeHoareAnnotation) {
					Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					m_Haf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case DFA_HOPCROFT_ARRAYS: {
				MinimizeDfaHopcroftPaper<CodeBlock, IPredicate> minimizeOp = new MinimizeDfaHopcroftPaper<CodeBlock, IPredicate>(
						new AutomataLibraryServices(m_Services), newAbstraction, predicateFactoryRefinement, partition,
						m_ComputeHoareAnnotation);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
						minimizeOp.getResult())).getResult();
				if (m_ComputeHoareAnnotation) {
					Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					m_Haf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case DFA_HOPCROFT_LISTS: {
				MinimizeIncompleteDfa<CodeBlock, IPredicate> minimizeOp = new MinimizeIncompleteDfa<CodeBlock, IPredicate>(
						new AutomataLibraryServices(m_Services), newAbstraction, predicateFactoryRefinement, partition,
						m_ComputeHoareAnnotation);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services),
						minimizeOp.getResult())).getResult();
				if (m_ComputeHoareAnnotation) {
					Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					m_Haf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case NONE:
				minimized = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
				break;
			default:
				throw new AssertionError();
			}
			int newSize = minimized.size();
			m_Abstraction = minimized;
			if (oldSize != 0 && oldSize < newSize) {
				throw new AssertionError("Minimization increased state space");
			}
			m_CegarLoopBenchmark.announceStatesRemovedByMinimization(oldSize - newSize);
		} finally {
			m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AutomataMinimizationTime);
		}
	}

	// private static Collection<Set<IPredicate>>
	// computePartitionDistinguishFinalNonFinal(
	// INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton, Logger
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
		Collection<IPredicate> states = automaton.getStates();
		Map<ProgramPoint, Set<IPredicate>> pp2p = new HashMap<ProgramPoint, Set<IPredicate>>();
		for (IPredicate p : states) {
			ISLPredicate sp = (ISLPredicate) p;
			pigeonHole(pp2p, sp);
		}
		Collection<Set<IPredicate>> partition = new ArrayList<Set<IPredicate>>();
		for (ProgramPoint pp : pp2p.keySet()) {
			Set<IPredicate> statesWithSamePP = pp2p.get(pp);
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
			INestedWordAutomaton<CodeBlock, IPredicate> interpolAutomaton) throws OperationCanceledException {
		mLogger.debug("Start determinization");
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> dia;
		switch (m_Pref.interpolantAutomatonEnhancement()) {
		case NONE:
			PowersetDeterminizer<CodeBlock, IPredicate> psd = new PowersetDeterminizer<CodeBlock, IPredicate>(
					interpolAutomaton, true, m_PredicateFactoryInterpolantAutomata);
			DeterminizeDD<CodeBlock, IPredicate> dabps = new DeterminizeDD<CodeBlock, IPredicate>(
					new AutomataLibraryServices(m_Services), interpolAutomaton, psd);
			dia = dabps.getResult();
			break;
		case BESTAPPROXIMATION_DEPRECATED:
			BestApproximationDeterminizer bed = new BestApproximationDeterminizer(m_SmtManager, m_Pref,
					(NestedWordAutomaton<CodeBlock, IPredicate>) interpolAutomaton,
					m_PredicateFactoryInterpolantAutomata);
			DeterminizeDD<CodeBlock, IPredicate> dab = new DeterminizeDD<CodeBlock, IPredicate>(
					new AutomataLibraryServices(m_Services), interpolAutomaton, bed);
			dia = dab.getResult();
			break;
		case SELFLOOP:
			SelfloopDeterminizer sed = new SelfloopDeterminizer(m_SmtManager, m_Pref, interpolAutomaton,
					m_PredicateFactoryInterpolantAutomata);
			DeterminizeDD<CodeBlock, IPredicate> dabsl = new DeterminizeDD<CodeBlock, IPredicate>(
					new AutomataLibraryServices(m_Services), interpolAutomaton, sed);
			dia = dabsl.getResult();
			break;
		default:
			throw new UnsupportedOperationException();
		}

		if (m_ComputeHoareAnnotation) {
			assert (new InductivityCheck(m_Services, dia, false, true,
					new IncrementalHoareTripleChecker(m_SmtManager, m_ModGlobVarManager)))
							.getResult() : "Not inductive";
		}
		if (m_Pref.dumpAutomata()) {
			String filename = "InterpolantAutomatonDeterminized_Iteration" + m_Iteration;
			writeAutomatonToFile(dia, filename);
		}
		assert (accepts(m_Services, dia, m_Counterexample.getWord()));
		mLogger.debug("Sucessfully determinized");
		return dia;
	}

	@Override
	protected void computeCFGHoareAnnotation() {
		if (m_SmtManager.isLocked()) {
			throw new AssertionError("SMTManager must not be locked at the beginning of Hoare annotation computation");
		}
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> abstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		new HoareAnnotationExtractor(m_Services, abstraction, m_Haf);
		(new HoareAnnotationWriter(m_RootNode.getRootAnnot(), m_SmtManager, m_Haf, m_Services))
				.addHoareAnnotationToCFG();
	}

	@Override
	public IElement getArtifact() {
		if (m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref.artifact() == Artifact.INTERPOLANT_AUTOMATON
				|| m_Pref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {

			if (m_ArtifactAutomaton == null) {
				mLogger.warn("Preferred Artifact not available," + " visualizing the RCFG instead");
				return m_RootNode;
			} else {
				try {
					return Automaton2UltimateModel.ultimateModel(new AutomataLibraryServices(m_Services),
							m_ArtifactAutomaton);
				} catch (OperationCanceledException e) {
					return null;
				}
			}
		} else if (m_Pref.artifact() == Artifact.RCFG) {
			return m_RootNode;
		} else {
			throw new IllegalArgumentException();
		}
	}

	public void howDifferentAreInterpolants(Collection<IPredicate> predicates) {
		int implications = 0;
		int biimplications = 0;
		IPredicate[] array = predicates.toArray(new IPredicate[0]);
		for (int i = 0; i < array.length; i++) {
			for (int j = 0; j < i; j++) {
				boolean implies = (m_SmtManager.isCovered(array[i], array[j]) == LBool.UNSAT);
				boolean explies = (m_SmtManager.isCovered(array[j], array[i]) == LBool.UNSAT);
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
			Word<CodeBlock> word) throws OperationCanceledException {
		try {
			return (new Accepts<CodeBlock, IPredicate>(new AutomataLibraryServices(services), nia,
					NestedWord.nestedWord(word), false, false)).getResult();
		} catch (AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}

	public CegarLoopBenchmarkGenerator getCegarLoopBenchmark() {
		return m_CegarLoopBenchmark;
	}

	/**
	 * method called at the end of the cegar loop
	 */
	public void finish() {
		// do nothing
	}

	public void setWitnessAutomaton(NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		m_WitnessAutomaton = witnessAutomaton;

	}

}
