/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Mostafa Mahmoud Amin
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Stack;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.RCFG2AnnotatedRCFG;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.Checker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.RedirectionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.emptinesscheck.IEmptinessCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.emptinesscheck.NWAEmptinessCheck;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.ImpulsChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.ImpulseChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.kojak.UltimateChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap4;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */

enum Result {
	CORRECT, TIMEOUT, MAXEDITERATIONS, UNKNOWN, INCORRECT
}

public class CodeCheckObserver implements IUnmanagedObserver {

	protected final static String s_SizeOfPredicatesFP = "SizeOfPredicatesFP";
	protected final static String s_SizeOfPredicatesBP = "SizeOfPredicatesBP";
	protected final static String s_NumberOfQuantifiedPredicates = "NumberOfQuantifiedPredicates";
	protected final static String s_ConjunctsInSSA = "Conjuncts in SSA";
	protected final static String s_ConjunctsInUnsatCore = "Conjuncts in UnsatCore";
	protected final static String s_NumberOfCodeBlocks = "NumberOfCodeBlocks";

	public final ILogger mLogger;
	private CodeChecker codeChecker;

	RootNode moriginalRoot;
	// TAPreferences mtaPrefs;
	ImpRootNode mgraphRoot;

	SmtManager msmtManager;
	public PredicateUnifier _predicateUnifier;
	IHoareTripleChecker medgeChecker;

	GraphWriter _graphWriter;

	NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> _satTriples;
	NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> _unsatTriples;
	NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> _satQuadruples;
	NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> _unsatQuadruples;
	Collection<ProgramPoint> mErrNodesOfAllProc;
	private final IUltimateServiceProvider mservices;
	private IToolchainStorage mtoolchainStorage;

	private static final boolean DEBUG = false;

	boolean loop_forever = true; // for DEBUG
	int iterationsLimit = -1; // for DEBUG
	private boolean outputHoareAnnotation = false;

	CodeCheckObserver(IUltimateServiceProvider services, IToolchainStorage toolchainStorage) {
		mservices = services;
		mLogger = mservices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mtoolchainStorage = toolchainStorage;
	}

	/**
	 * Initialize all the required objects in the implementation.
	 * 
	 * @param root
	 * @return
	 */
	public boolean initialize(IElement root) {
		readPreferencePage();

		moriginalRoot = (RootNode) root;
		RootAnnot rootAnnot = moriginalRoot.getRootAnnot();

		msmtManager = new SmtManager(rootAnnot.getScript(), rootAnnot.getBoogie2SMT(),
				rootAnnot.getModGlobVarManager(), mservices, false, rootAnnot.getManagedScript());

		_predicateUnifier = new PredicateUnifier(mservices, msmtManager);

		medgeChecker = new MonolithicHoareTripleChecker(msmtManager.getManagedScript(), msmtManager.getModifiableGlobals());

		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		mErrNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			mErrNodesOfAllProc.addAll(errNodeOfProc);
		}

		if (GlobalSettings._instance._memoizeNormalEdgeChecks) {
			_satTriples = new NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained>();
			_unsatTriples = new NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained>();
		}
		if (GlobalSettings._instance._memoizeReturnEdgeChecks) {
			_satQuadruples = new NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained>();
			_unsatQuadruples = new NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained>();
		}
		_graphWriter = new GraphWriter(GlobalSettings._instance._dotGraphPath, true, true, true, false,
				msmtManager.getScript());

		//DD: removed dependency to AIMK2, will be replaced by AIv2 soon 
//		boolean usePredicatesFromAbstractInterpretation = true; // TODO make a Pref
		Map<RCFGNode, Term> initialPredicates = null;
//		if (usePredicatesFromAbstractInterpretation) {
//			AbstractInterpretationPredicates annot = AbstractInterpretationPredicates.getAnnotation(moriginalRoot);
//			if (annot != null) {
//				initialPredicates = annot.getPredicates();
//			} else {
//				mLogger.warn(
//						"was not able to retrieve initial predicates from abstract interpretation --> wrong toolchain?? (using \"true\")");
//				initialPredicates = null;
//			}
//		}
		//end dependency removal
		RCFG2AnnotatedRCFG r2ar = new RCFG2AnnotatedRCFG(msmtManager, mLogger, _predicateUnifier.getTruePredicate(),
				initialPredicates);
		mgraphRoot = r2ar.convert(mservices, moriginalRoot);

		_graphWriter.writeGraphAsImage(mgraphRoot,
				String.format("graph_%s_originalAfterConversion", _graphWriter._graphCounter));

		removeSummaryEdges();

		_graphWriter.writeGraphAsImage(mgraphRoot,
				String.format("graph_%s_originalSummaryEdgesRemoved", _graphWriter._graphCounter));

		if (GlobalSettings._instance.checker == Checker.IMPULSE) {
			codeChecker = new ImpulseChecker(root, msmtManager, moriginalRoot, mgraphRoot, _graphWriter,
					medgeChecker, _predicateUnifier, mLogger);
		} else {
			codeChecker = new UltimateChecker(root, msmtManager, moriginalRoot, mgraphRoot, _graphWriter,
					medgeChecker, _predicateUnifier, mLogger);
		}
		iterationsLimit = GlobalSettings._instance._iterations;
		loop_forever = (iterationsLimit == -1);

		return false;
	}

	private void readPreferencePage() {
		RcpPreferenceProvider prefs = new RcpPreferenceProvider(Activator.PLUGIN_ID);

		GlobalSettings.init();

		GlobalSettings._instance.checker = prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_CHECKER, Checker.class);

		GlobalSettings._instance._memoizeNormalEdgeChecks = prefs.getBoolean(
				CodeCheckPreferenceInitializer.LABEL_MEMOIZENORMALEDGECHECKS,
				CodeCheckPreferenceInitializer.DEF_MEMOIZENORMALEDGECHECKS);
		GlobalSettings._instance._memoizeReturnEdgeChecks = prefs.getBoolean(
				CodeCheckPreferenceInitializer.LABEL_MEMOIZERETURNEDGECHECKS,
				CodeCheckPreferenceInitializer.DEF_MEMOIZERETURNEDGECHECKS);

//		GlobalSettings._instance._solverAndInterpolator = prefs
//				.getEnum(CodeCheckPreferenceInitializer.LABEL_SOLVERANDINTERPOLATOR, SolverAndInterpolator.class);

		GlobalSettings._instance._interpolationMode = prefs
				.getEnum(CodeCheckPreferenceInitializer.LABEL_INTERPOLATIONMODE, INTERPOLATION.class);

		GlobalSettings._instance.useInterpolantconsolidation = prefs.getBoolean(
				CodeCheckPreferenceInitializer.LABEL_INTERPOLANTCONSOLIDATION,
				CodeCheckPreferenceInitializer.DEF_INTERPOLANTCONSOLIDATION);

		GlobalSettings._instance._predicateUnification = prefs
				.getEnum(CodeCheckPreferenceInitializer.LABEL_PREDICATEUNIFICATION, PredicateUnification.class);

		GlobalSettings._instance._edgeCheckOptimization = prefs
				.getEnum(CodeCheckPreferenceInitializer.LABEL_EDGECHECKOPTIMIZATION, EdgeCheckOptimization.class);

		GlobalSettings._instance._iterations = prefs.getInt(CodeCheckPreferenceInitializer.LABEL_ITERATIONS,
				CodeCheckPreferenceInitializer.DEF_ITERATIONS);

		GlobalSettings._instance._dotGraphPath = prefs.getString(CodeCheckPreferenceInitializer.LABEL_GRAPHWRITERPATH,
				CodeCheckPreferenceInitializer.DEF_GRAPHWRITERPATH);

		GlobalSettings._instance.redirectionStrategy = prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_REDIRECTION,
				RedirectionStrategy.class);

		GlobalSettings._instance.defaultRedirection = prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_DEF_RED,
				CodeCheckPreferenceInitializer.DEF_DEF_RED);
		GlobalSettings._instance.removeFalseNodes = prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_RmFALSE,
				CodeCheckPreferenceInitializer.DEF_RmFALSE);
		GlobalSettings._instance.checkSatisfiability = prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_CHK_SAT,
				CodeCheckPreferenceInitializer.DEF_CHK_SAT);

		/*
		 * Settings concerning the solver for trace checks
		 */
		GlobalSettings._instance.useSeparateSolverForTracechecks = prefs.getBoolean(
				CodeCheckPreferenceInitializer.LABEL_USESEPARATETRACECHECKSOLVER,
				CodeCheckPreferenceInitializer.DEF_USESEPARATETRACECHECKSOLVER);

		GlobalSettings._instance.useFallbackForSeparateSolverForTracechecks = prefs.getBoolean(
				CodeCheckPreferenceInitializer.LABEL_USEFALLBACKFORSEPARATETRACECHECKSOLVER,
				CodeCheckPreferenceInitializer.DEF_USEFALLBACKFORSEPARATETRACECHECKSOLVER);
		
		GlobalSettings._instance.chooseSeparateSolverForTracechecks = prefs.getEnum(
				CodeCheckPreferenceInitializer.LABEL_CHOOSESEPARATETRACECHECKSOLVER,
				SolverMode.class);

		GlobalSettings._instance.separateSolverForTracechecksCommand = prefs.getString(
				CodeCheckPreferenceInitializer.LABEL_SEPARATETRACECHECKSOLVERCOMMAND,
				CodeCheckPreferenceInitializer.DEF_SEPARATETRACECHECKSOLVERCOMMAND);

		GlobalSettings._instance.separateSolverForTracechecksTheory = prefs.getString(
				CodeCheckPreferenceInitializer.LABEL_SEPARATETRACECHECKSOLVERTHEORY,
				CodeCheckPreferenceInitializer.DEF_SEPARATETRACECHECKSOLVERTHEORY);

		/*
		 * Settings concerning betim interpolation
		 */
		GlobalSettings._instance.useLiveVariables = prefs.getBoolean(
				CodeCheckPreferenceInitializer.LABEL_LIVE_VARIABLES,
				true);
		GlobalSettings._instance.useUnsatCores = prefs.getEnum(
				CodeCheckPreferenceInitializer.LABEL_UNSAT_CORES,
				UnsatCores.class);


	}

	private void removeSummaryEdges() {
		Stack<AnnotatedProgramPoint> stack = new Stack<AnnotatedProgramPoint>();
		HashSet<AnnotatedProgramPoint> visited = new HashSet<AnnotatedProgramPoint>();
		visited.add(mgraphRoot);
		stack.add(mgraphRoot);
		while (!stack.isEmpty()) {
			AnnotatedProgramPoint node = stack.pop();
			AppEdge[] outEdges = node.getOutgoingEdges().toArray(new AppEdge[] {});
			for (AppEdge outEdge : outEdges) {
				AnnotatedProgramPoint successor = outEdge.getTarget();
				if (outEdge.getStatement() instanceof Summary) {
					if (((Summary) outEdge.getStatement()).calledProcedureHasImplementation())
						outEdge.disconnect();
				}
				if (!visited.contains(successor)) {
					visited.add(successor);
					stack.add(successor);
				}
			}
		}
	}

	@Override
	public boolean process(IElement root) {
		initialize(root);

		_graphWriter.writeGraphAsImage(mgraphRoot, String.format("graph_%s_original", _graphWriter._graphCounter));

		ImpRootNode originalGraphCopy = copyGraph(mgraphRoot);

		_graphWriter.writeGraphAsImage(originalGraphCopy,
				String.format("graph_%s_originalCopied", _graphWriter._graphCounter));

		ArrayList<AnnotatedProgramPoint> procRootsToCheck = new ArrayList<AnnotatedProgramPoint>();

		// check for Ultimate.start -- assuming that if such a procedure exists,
		// it comes from the c translation
		for (AnnotatedProgramPoint procRoot : mgraphRoot.getOutgoingNodes()) {
			if (procRoot.getProgramPoint().getProcedure().startsWith("ULTIMATE.start")) {
				procRootsToCheck.add(procRoot);
				break;
			}
		}
		if (procRootsToCheck.isEmpty()) { // -> no Ultimate.start present
			procRootsToCheck.addAll(mgraphRoot.getOutgoingNodes());
		}

		Result overallResult = Result.UNKNOWN;
		boolean allSafe = true;
		boolean verificationInterrupted = false;
		RcfgProgramExecution realErrorProgramExecution = null;

		// benchmark data collector variables
		CegarLoopStatisticsGenerator benchmarkGenerator =  new CegarLoopStatisticsGenerator();
		benchmarkGenerator.start(CegarLoopStatisticsDefinitions.OverallTime.toString());

		int iterationsCount = 0;

		InterpolatingTraceChecker traceChecker = null;

		for (AnnotatedProgramPoint procedureRoot : procRootsToCheck) {
			if (!mservices.getProgressMonitorService().continueProcessing()) {
				verificationInterrupted = true;
				break;
			}

			mLogger.debug("Exploring : " + procedureRoot);

			IEmptinessCheck emptinessCheck = new NWAEmptinessCheck(mservices);

			if (DEBUG)
				codeChecker.debug();
			while (loop_forever | iterationsCount++ < iterationsLimit) {
				if (!mservices.getProgressMonitorService().continueProcessing()) {
					verificationInterrupted = true;
					break;
				}
				
				benchmarkGenerator.announceNextIteration();

				mLogger.debug(String.format("Iterations = %d\n", iterationsCount));
				NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun = emptinessCheck.checkForEmptiness(procedureRoot);

				if (errorRun == null) {
					// TODO: this only works for the case where we have 1 procedure in procRootsToCheck, right??
					_graphWriter.writeGraphAsImage(procedureRoot, String.format("graph_%s_%s_noEP",
							_graphWriter._graphCounter, procedureRoot.toString().substring(0, 5)));
					// if an error trace doesn't exist, return safe
					mLogger.warn("This Program is SAFE, Check terminated with " + iterationsCount + " iterations.");
					break;
				} else {
					mLogger.info("Error Path is FOUND.");
					_graphWriter.writeGraphAsImage(procedureRoot,
							String.format("graph_%s_%s_foundEP", _graphWriter._graphCounter,
									procedureRoot.toString().substring(0, 5)),
							errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[] {}));

					if (GlobalSettings._instance._predicateUnification == PredicateUnification.PER_ITERATION)
						_predicateUnifier = new PredicateUnifier(mservices, msmtManager);

					SmtManager smtManagerTracechecks;
//					if (noArrayOrNIRAsofar && GlobalSettings._instance.useSeparateSolverForTracechecks) {
					if (GlobalSettings._instance.useSeparateSolverForTracechecks) {
						final String filename = moriginalRoot.getFilename() + "_TraceCheck_Iteration" + iterationsCount;
						final SolverMode solverMode = GlobalSettings._instance.chooseSeparateSolverForTracechecks;
						final String commandExternalSolver = GlobalSettings._instance.separateSolverForTracechecksCommand;
						final boolean dumpSmtScriptToFile = false;
						final String pathOfDumpedScript = "";
						final Settings solverSettings = SolverBuilder.constructSolverSettings(
								filename, solverMode, commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
						final Script tcSolver = SolverBuilder.buildAndInitializeSolver(mservices, mtoolchainStorage,
								GlobalSettings._instance.chooseSeparateSolverForTracechecks,
								solverSettings, false, 
								false, 
								GlobalSettings._instance.separateSolverForTracechecksTheory,
								"TraceCheck_Iteration" + iterationsCount);

						smtManagerTracechecks = new SmtManager(tcSolver, moriginalRoot.getRootAnnot().getBoogie2SMT(),
								moriginalRoot.getRootAnnot().getModGlobVarManager(), mservices, false, moriginalRoot.getRootAnnot().getManagedScript());
						TermTransferrer tt = new TermTransferrer(tcSolver);
						for (Term axiom : moriginalRoot.getRootAnnot().getBoogie2SMT().getAxioms()) {
							tcSolver.assertTerm(tt.transform(axiom));
						}
					} else {
						smtManagerTracechecks = msmtManager;
					}

					traceChecker = null;
					switch (GlobalSettings._instance._interpolationMode) {
					case Craig_TreeInterpolation:
					case Craig_NestedInterpolation:
						try {
							traceChecker = new InterpolatingTraceCheckerCraig(_predicateUnifier.getTruePredicate(),
									_predicateUnifier.getFalsePredicate(), // return LBool.UNSAT if trace
									// is infeasible
									new TreeMap<Integer, IPredicate>(), errorRun.getWord(), msmtManager,
									moriginalRoot.getRootAnnot().getModGlobVarManager(),
									/*
									 * TODO : When Matthias introduced this parameter he set the argument to
									 * AssertCodeBlockOrder.NOT_INCREMENTALLY . Check if you want to set this to a different
									 * value.
									 */AssertCodeBlockOrder.NOT_INCREMENTALLY, mservices, true, _predicateUnifier,
									 GlobalSettings._instance._interpolationMode, smtManagerTracechecks, true);
							//							} catch (UnsupportedOperationException uoe) {
						} catch (Exception e) {
							if (!GlobalSettings._instance.useFallbackForSeparateSolverForTracechecks)
								throw e;
							/*
							 * The fallback tracechecker is always the normal solver (i.e. the smtManager that was set in RCFGBuilder settings
							 * with forward predicates betim interpolation.
							 */
							traceChecker = new TraceCheckerSpWp(_predicateUnifier.getTruePredicate(),
									_predicateUnifier.getFalsePredicate(), new TreeMap<Integer, IPredicate>(),
									errorRun.getWord(), msmtManager, moriginalRoot.getRootAnnot().getModGlobVarManager(),
									AssertCodeBlockOrder.NOT_INCREMENTALLY, 
									UnsatCores.CONJUNCT_LEVEL, 
									true, mservices,
									true, _predicateUnifier, INTERPOLATION.ForwardPredicates, //fallback interpolation mode hardcoded for now
									msmtManager);
						}
						break;
					case ForwardPredicates:
					case BackwardPredicates:
					case FPandBP:
						// return LBool.UNSAT if trace is infeasible
						/*
						 * TODO : When Matthias introduced this parameter he set the argument to
						 * AssertCodeBlockOrder.NOT_INCREMENTALLY . Check if you want to set this to a different value.
						 */
						try {
							traceChecker = new TraceCheckerSpWp(_predicateUnifier.getTruePredicate(),
									_predicateUnifier.getFalsePredicate(), new TreeMap<Integer, IPredicate>(),
									errorRun.getWord(), msmtManager, moriginalRoot.getRootAnnot().getModGlobVarManager(),
									AssertCodeBlockOrder.NOT_INCREMENTALLY, 
									GlobalSettings._instance.useUnsatCores,
									GlobalSettings._instance.useLiveVariables,
									mservices,
									true, _predicateUnifier, GlobalSettings._instance._interpolationMode,
									smtManagerTracechecks);
						} catch (Exception e) {
							if (!GlobalSettings._instance.useFallbackForSeparateSolverForTracechecks)
								throw e;

							traceChecker = new TraceCheckerSpWp(_predicateUnifier.getTruePredicate(),
									_predicateUnifier.getFalsePredicate(), new TreeMap<Integer, IPredicate>(),
									errorRun.getWord(), msmtManager, moriginalRoot.getRootAnnot().getModGlobVarManager(),
									AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true, mservices,
									true, _predicateUnifier, GlobalSettings._instance._interpolationMode,
									msmtManager);
						}
						break;
					case PathInvariants:
						throw new UnsupportedOperationException("alex: i don't know what this setting is for");
					}

					if (GlobalSettings._instance.useSeparateSolverForTracechecks) {
						smtManagerTracechecks.getScript().exit();
					}

					if (traceChecker.getToolchainCancelledExpection() != null) {
						throw traceChecker.getToolchainCancelledExpection();
					}

					LBool isSafe = traceChecker.isCorrect();
					benchmarkGenerator.addTraceCheckerData(traceChecker.getTraceCheckerBenchmark());
					
					if (isSafe == LBool.UNSAT) { // trace is infeasible
						IPredicate[] interpolants = null;

						if (GlobalSettings._instance.useInterpolantconsolidation) {
							try {

								InterpolantConsolidation interpConsoli = new InterpolantConsolidation(
										_predicateUnifier.getTruePredicate(), _predicateUnifier.getFalsePredicate(),
										new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(errorRun.getWord()),
										msmtManager, moriginalRoot.getRootAnnot().getModGlobVarManager(), mservices,
										mLogger, _predicateUnifier, traceChecker, null// mtaPrefs
								);
								// Add benchmark data of interpolant consolidation
								// mCegarLoopBenchmark.addInterpolationConsolidationData(interpConsoli.getInterpolantConsolidationBenchmarks());
								// mInterpolantGenerator = interpConsoli;
								interpolants = interpConsoli.getInterpolants();
							} catch (AutomataOperationCanceledException e) {
								// Timeout
								e.printStackTrace();
							}
						} else {
							interpolants = traceChecker.getInterpolants();
						}

						if (GlobalSettings._instance._memoizeNormalEdgeChecks
								&& GlobalSettings._instance._memoizeReturnEdgeChecks)
							codeChecker.codeCheck(errorRun, interpolants, procedureRoot, _satTriples, _unsatTriples,
									_satQuadruples, _unsatQuadruples);
						else if (GlobalSettings._instance._memoizeNormalEdgeChecks
								&& !GlobalSettings._instance._memoizeReturnEdgeChecks)
							codeChecker.codeCheck(errorRun, interpolants, procedureRoot, _satTriples, _unsatTriples);
						else
							codeChecker.codeCheck(errorRun, interpolants, procedureRoot);

						benchmarkGenerator.addEdgeCheckerData(codeChecker._edgeChecker.getEdgeCheckerBenchmark());

					} else { // trace is feasible
						mLogger.warn(
								"This program is UNSAFE, Check terminated with " + iterationsCount + " iterations.");
						allSafe = false;
						realErrorProgramExecution = traceChecker.getRcfgProgramExecution();

						if (DEBUG)
							codeChecker.debug();
						break;
					}
				}
				if (DEBUG)
					codeChecker.debug();
			}
			// we need a fresh copy for each iteration because..??
			mgraphRoot = copyGraph(originalGraphCopy);
			codeChecker.mgraphRoot = mgraphRoot;

			if (!allSafe)
				break;
		}

		if (DEBUG)
			codeChecker.debug();

		if (!verificationInterrupted) {
			if (allSafe) {
				overallResult = Result.CORRECT;
			}
			else
				overallResult = Result.INCORRECT;
		} else {
			reportTimeoutResult(mErrNodesOfAllProc);
		}

		mLogger.debug("MemoizationHitsSat: " + codeChecker.memoizationHitsSat);
		mLogger.debug("MemoizationHitsUnsat: " + codeChecker.memoizationHitsUnsat);
		mLogger.debug("MemoizationReturnHitsSat: " + codeChecker.memoizationReturnHitsSat);
		mLogger.debug("MemoizationReturnHitsUnsat: " + codeChecker.memoizationReturnHitsUnsat);

		
		//benchmark stuff
		benchmarkGenerator.setResult(overallResult);
		benchmarkGenerator.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());

		CodeCheckBenchmarks ccb = new CodeCheckBenchmarks(moriginalRoot.getRootAnnot());
		ccb.aggregateBenchmarkData(benchmarkGenerator);

		reportBenchmark(ccb);

		if (overallResult == Result.CORRECT) {
			reportPositiveResults(mErrNodesOfAllProc);

			if (outputHoareAnnotation) {
				for (AnnotatedProgramPoint pr : procRootsToCheck) {
					mLogger.info("Hoare annotation for entrypoint " + pr.getProgramPoint().getProcedure());
					HashMap<ProgramPoint, Term> ha = computeHoareAnnotation(pr);
					for (Entry<ProgramPoint, Term> kvp : ha.entrySet()) {
						mLogger.info("At program point  " + prettyPrintProgramPoint(kvp.getKey())
								+ "  the Hoare annotation is:  " + kvp.getValue());
					}
				}
			}
		} else if (overallResult == Result.INCORRECT) {
			reportCounterexampleResult(realErrorProgramExecution);
		} else {
			String shortDescription = "Unable to decide if program is safe!";
			String longDescription = "Unable to decide if program is safe!";
			GenericResult result = new GenericResult(Activator.PLUGIN_NAME, shortDescription, longDescription,
					Severity.INFO);
			mservices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		}

		return false;
	}

	// taken from TraceAbstractionStarter
	private static String prettyPrintProgramPoint(ProgramPoint pp) {
		int startLine = pp.getPayload().getLocation().getStartLine();
		int endLine = pp.getPayload().getLocation().getStartLine();
		StringBuilder sb = new StringBuilder();
		sb.append(pp);
		if (startLine == endLine) {
			sb.append("(line " + startLine + ")");
		} else {
			sb.append("(lines " + startLine + " " + endLine + ")");
		}
		return sb.toString();
	}

	private HashMap<ProgramPoint, Term> computeHoareAnnotation(AnnotatedProgramPoint pr) {
		HashMap<ProgramPoint, HashSet<AnnotatedProgramPoint>> programPointToAnnotatedProgramPoints = new HashMap<>();

		HashMap<ProgramPoint, Term> programPointToHoareAnnotation = new HashMap<>();

		computeProgramPointToAnnotatedProgramPoints(pr, programPointToAnnotatedProgramPoints);

		for (Entry<ProgramPoint, HashSet<AnnotatedProgramPoint>> kvp : programPointToAnnotatedProgramPoints
				.entrySet()) {
			IPredicate annot = msmtManager.getPredicateFactory().newPredicate(
					msmtManager.getScript().term("false")); 

			for (AnnotatedProgramPoint app : kvp.getValue()) {
				Term tvp = msmtManager.getPredicateFactory().or(false, annot, app.getPredicate());
				annot = msmtManager.getPredicateFactory().newSPredicate(kvp.getKey(), tvp);
			}
			// programPointToHoareAnnotation.put(kvp.getKey(), annot.getClosedFormula());
			programPointToHoareAnnotation.put(kvp.getKey(), annot.getFormula());
		}
		return programPointToHoareAnnotation;
	}

	/**
	 * fill up the map programPointToAnnotatedProgramPoints with the reachable part of the CFG
	 * 
	 * @param annotatedProgramPoint
	 * @param programPointToAnnotatedProgramPoints
	 */
	private void computeProgramPointToAnnotatedProgramPoints(AnnotatedProgramPoint entry,
			HashMap<ProgramPoint, HashSet<AnnotatedProgramPoint>> programPointToAnnotatedProgramPoints) {

		HashSet<AnnotatedProgramPoint> visited = new HashSet<>();

		ArrayDeque<AnnotatedProgramPoint> queue = new ArrayDeque<>();

		queue.push(entry);

		while (!queue.isEmpty()) {
			AnnotatedProgramPoint current = queue.pop();

			HashSet<AnnotatedProgramPoint> apps = programPointToAnnotatedProgramPoints.get(current.getProgramPoint());
			if (apps == null) {
				apps = new HashSet<AnnotatedProgramPoint>();
				programPointToAnnotatedProgramPoints.put(current.getProgramPoint(), apps);
			}
			apps.add(current);

			for (AppEdge outEdge : current.getOutgoingEdges()) {
				if (!visited.contains(outEdge.getTarget())) {
					queue.push(outEdge.getTarget());
					visited.add(outEdge.getTarget());
				}
			}
		}
	}

	/**
	 * Given a graph root, copy all the nodes and the corresponding connections.
	 * 
	 * @param root
	 * @return
	 */
	public ImpRootNode copyGraph(ImpRootNode root) {
		HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> copy = new HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint>();
		ImpRootNode newRoot = new ImpRootNode(root.getRootAnnot());
		copy.put(root, newRoot);
		Stack<AnnotatedProgramPoint> stack = new Stack<AnnotatedProgramPoint>();
		for (AnnotatedProgramPoint child : root.getOutgoingNodes()) {
			stack.add(child);
		}
		while (!stack.isEmpty()) {
			AnnotatedProgramPoint current = stack.pop();
			if (copy.containsKey(current))
				continue;
			copy.put(current, new AnnotatedProgramPoint(current));
			List<AnnotatedProgramPoint> nextNodes = current.getOutgoingNodes();
			for (AnnotatedProgramPoint nextNode : nextNodes) {
				if (!copy.containsKey(nextNode)) {
					stack.add(nextNode);
				}
			}
		}
		for (Entry<AnnotatedProgramPoint, AnnotatedProgramPoint> entry : copy.entrySet()) {
			AnnotatedProgramPoint oldNode = entry.getKey();
			AnnotatedProgramPoint newNode = entry.getValue();
			for (AppEdge outEdge : oldNode.getOutgoingEdges()) {
				if (outEdge instanceof AppHyperEdge) {
					AppHyperEdge outHypEdge = (AppHyperEdge) outEdge;
					AnnotatedProgramPoint hier = copy.get(outHypEdge.getHier());
					if (hier != null)
						newNode.connectOutgoingReturn(hier, (Return) outHypEdge.getStatement(),
								copy.get(outHypEdge.getTarget()));
				} else {
					newNode.connectOutgoing(outEdge.getStatement(), copy.get(outEdge.getTarget()));
				}
			}
		}
		return newRoot;
	}

	private <T> void reportBenchmark(ICsvProviderProvider<T> benchmark) {
		String shortDescription = "Ultimate CodeCheck benchmark data";
		BenchmarkResult<T> res = new BenchmarkResult<T>(Activator.PLUGIN_NAME, shortDescription, benchmark);
		// s_Logger.warn(res.getLongDescription());

		reportResult(res);
	}

	private void reportPositiveResults(Collection<ProgramPoint> errorLocs) {
		final String longDescription;
		if (errorLocs.isEmpty()) {
			longDescription = "We were not able to verify any"
					+ " specifiation because the program does not contain any specification.";
		} else {
			longDescription = errorLocs.size() + " specifications checked. All of them hold";
			for (ProgramPoint errorLoc : errorLocs) {
				PositiveResult<RcfgElement> pResult = new PositiveResult<RcfgElement>(Activator.PLUGIN_NAME, errorLoc,
						mservices.getBacktranslationService());
				reportResult(pResult);
			}
		}
		AllSpecificationsHoldResult result = new AllSpecificationsHoldResult(Activator.PLUGIN_NAME, longDescription);
		reportResult(result);
		mLogger.info(result.getShortDescription() + " " + result.getLongDescription());
	}

	private void reportCounterexampleResult(RcfgProgramExecution pe) {
		if (!pe.getOverapproximations().isEmpty()) {
			reportUnproveableResult(pe, pe.getUnprovabilityReasons());
			return;
		}

		reportResult(new CounterExampleResult<RcfgElement, RCFGEdge, Expression>(getErrorPP(pe),
				Activator.PLUGIN_NAME, mservices.getBacktranslationService(), pe));
	}

	private void reportUnproveableResult(RcfgProgramExecution pe, List<UnprovabilityReason> unproabilityReasons) {
		ProgramPoint errorPP = getErrorPP(pe);
		UnprovableResult<RcfgElement, RCFGEdge, Expression> uknRes = new UnprovableResult<RcfgElement, RCFGEdge, Expression>(
				Activator.PLUGIN_NAME, errorPP, mservices.getBacktranslationService(), pe, unproabilityReasons);
		reportResult(uknRes);
	}

	public ProgramPoint getErrorPP(RcfgProgramExecution rcfgProgramExecution) {
		int lastPosition = rcfgProgramExecution.getLength() - 1;
		RCFGEdge last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}

	private void reportTimeoutResult(Collection<ProgramPoint> errorLocs) {
		for (ProgramPoint errorIpp : errorLocs) {
			ProgramPoint errorLoc = errorIpp;
			ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage = "Unable to prove that "
					+ ResultUtil.getCheckedSpecification(errorLoc).getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			TimeoutResultAtElement<RcfgElement> timeOutRes = new TimeoutResultAtElement<RcfgElement>(errorLoc,
					Activator.PLUGIN_NAME, mservices.getBacktranslationService(), timeOutMessage);
			reportResult(timeOutRes);
			// s_Logger.warn(timeOutMessage);
		}
	}

	private void reportResult(IResult res) {
		mservices.getResultService().reportResult(Activator.PLUGIN_ID, res);
	}

	// Debug

	public ImpRootNode getRoot() {
		return codeChecker.mgraphRoot;
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub

	}

	@Override
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}
}
