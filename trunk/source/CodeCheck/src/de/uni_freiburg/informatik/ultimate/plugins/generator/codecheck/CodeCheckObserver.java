package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Stack;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.RCFG2AnnotatedRCFG;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.Checker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.SolverAndInterpolator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.emptinesscheck.IEmptinessCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.emptinesscheck.NWAEmptinessCheck;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.ImpulsChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.ImpulseChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.kojak.UltimateChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.ResultUtil;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */

enum Result {
	CORRECT, TIMEOUT, MAXEDITERATIONS, UNKNOWN, INCORRECT
}

public class CodeCheckObserver implements IUnmanagedObserver {

//	protected final static String s_SizeOfPredicates = "SizeOfPredicates";
	protected final static String s_SizeOfPredicatesFP = "SizeOfPredicatesFP";
	protected final static String s_SizeOfPredicatesBP = "SizeOfPredicatesBP";
	protected final static String s_NumberOfQuantifiedPredicates = "NumberOfQuantifiedPredicates";
	protected final static String s_ConjunctsInSSA = "Conjuncts in SSA";
	protected final static String s_ConjunctsInUnsatCore = "Conjuncts in UnsatCore";
	protected final static String s_NumberOfCodeBlocks = "NumberOfCodeBlocks";

	public final Logger mLogger;
	private CodeChecker codeChecker;

	RootNode m_originalRoot;
	TAPreferences m_taPrefs;
	ImpRootNode m_graphRoot;

	SmtManager m_smtManager;
//	IPredicate m_truePredicate;
//	IPredicate m_falsePredicate;
	PredicateUnifier _predicateUnifier;
	EdgeChecker m_edgeChecker;

	GraphWriter _graphWriter;

	HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> _satTriples;
	HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> _unsatTriples;
	HashMap<IPredicate, HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>> _satQuadruples;
	HashMap<IPredicate, HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>> _unsatQuadruples;
	Collection<ProgramPoint> mErrNodesOfAllProc;
	private final IUltimateServiceProvider mServices;

	private static final boolean DEBUG = false;
	

	boolean loop_forever = true; // for DEBUG
	int iterationsLimit = -1; // for DEBUG


	CodeCheckObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	/**
	 * Initialize all the required objects in the implementation.
	 * 
	 * @param root
	 * @return
	 */
	public boolean initialize(IElement root) {
		readPreferencePage();

		m_originalRoot = (RootNode) root;
		RootAnnot rootAnnot = m_originalRoot.getRootAnnot();
		m_smtManager = new SmtManager(rootAnnot.getBoogie2SMT(), rootAnnot.getModGlobVarManager(), mServices);

		_predicateUnifier = new PredicateUnifier(mServices, m_smtManager);

//		m_truePredicate = _predicateUnifier.getTruePredicate();
//		m_falsePredicate = _predicateUnifier.getFalsePredicate();

		m_edgeChecker = new EdgeChecker(m_smtManager, rootAnnot.getModGlobVarManager());

		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		mErrNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			mErrNodesOfAllProc.addAll(errNodeOfProc);
		}

		if (GlobalSettings._instance._memoizeNormalEdgeChecks) {
			_satTriples = new HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>();
			_unsatTriples = new HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>();
		}
		if (GlobalSettings._instance._memoizeReturnEdgeChecks) {
			_satQuadruples = new HashMap<IPredicate, HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>>();
			_unsatQuadruples = new HashMap<IPredicate, HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>>();
		}
		_graphWriter = new GraphWriter(GlobalSettings._instance._dotGraphPath, true, true, true, false,
				m_smtManager.getScript());

		RCFG2AnnotatedRCFG r2ar = new RCFG2AnnotatedRCFG(m_smtManager, mLogger);
		m_graphRoot = r2ar.convert(m_originalRoot, _predicateUnifier.getTruePredicate());

		_graphWriter.writeGraphAsImage(m_graphRoot,
				String.format("graph_%s_originalAfterConversion", _graphWriter._graphCounter));

		removeSummaryEdges();

		_graphWriter.writeGraphAsImage(m_graphRoot,
				String.format("graph_%s_originalSummaryEdgesRemoved", _graphWriter._graphCounter));

		if (GlobalSettings._instance.checker == Checker.IMPULSE) {
			codeChecker = new ImpulseChecker(root, m_smtManager, m_taPrefs,
					m_originalRoot, m_graphRoot, _graphWriter, m_edgeChecker, _predicateUnifier, mLogger);
		} else {
			codeChecker = new UltimateChecker(root, m_smtManager, m_taPrefs,
					m_originalRoot, m_graphRoot, _graphWriter, m_edgeChecker, _predicateUnifier, mLogger);
		}
		iterationsLimit = GlobalSettings._instance._iterations;
		loop_forever = (iterationsLimit == -1);
		
		return false;
	}

	private void readPreferencePage() {
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);

		GlobalSettings.init();

		GlobalSettings._instance.checker = prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_CHECKER, Checker.class);

		GlobalSettings._instance._memoizeNormalEdgeChecks = prefs.getBoolean(
				CodeCheckPreferenceInitializer.LABEL_MEMOIZENORMALEDGECHECKS,
				CodeCheckPreferenceInitializer.DEF_MEMOIZENORMALEDGECHECKS);
		GlobalSettings._instance._memoizeReturnEdgeChecks = prefs.getBoolean(
				CodeCheckPreferenceInitializer.LABEL_MEMOIZERETURNEDGECHECKS,
				CodeCheckPreferenceInitializer.DEF_MEMOIZERETURNEDGECHECKS);
		// GlobalSettings._instance._checkOnlyMain = prefs.getBoolean(
		// PreferenceInitializer.LABEL_ONLYMAINPROCEDURE,
		// PreferenceInitializer.DEF_ONLYMAINPROCEDURE);

		GlobalSettings._instance._solverAndInterpolator = prefs.getEnum(
				CodeCheckPreferenceInitializer.LABEL_SOLVERANDINTERPOLATOR, SolverAndInterpolator.class);

		GlobalSettings._instance._interpolationMode = prefs.getEnum(
				CodeCheckPreferenceInitializer.LABEL_INTERPOLATIONMODE, INTERPOLATION.class);

		GlobalSettings._instance._predicateUnification = prefs.getEnum(
				CodeCheckPreferenceInitializer.LABEL_PREDICATEUNIFICATION, PredicateUnification.class);

		GlobalSettings._instance._edgeCheckOptimization = prefs.getEnum(
				CodeCheckPreferenceInitializer.LABEL_EDGECHECKOPTIMIZATION, EdgeCheckOptimization.class);
		
		GlobalSettings._instance._iterations = prefs.getInt(CodeCheckPreferenceInitializer.LABEL_ITERATIONS,
				CodeCheckPreferenceInitializer.DEF_ITERATIONS);
		
		GlobalSettings._instance._dotGraphPath = prefs.getString(CodeCheckPreferenceInitializer.LABEL_GRAPHWRITERPATH, CodeCheckPreferenceInitializer.DEF_GRAPHWRITERPATH);

	}

	private void removeSummaryEdges() {
		Stack<AnnotatedProgramPoint> stack = new Stack<AnnotatedProgramPoint>();
		HashSet<AnnotatedProgramPoint> visited = new HashSet<AnnotatedProgramPoint>();
		visited.add(m_graphRoot);
		stack.add(m_graphRoot);
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

	public boolean process(IElement root) {
		initialize(root);

		_graphWriter.writeGraphAsImage(m_graphRoot, String.format("graph_%s_original", _graphWriter._graphCounter));

		ImpRootNode originalGraphCopy = copyGraph(m_graphRoot);

		_graphWriter.writeGraphAsImage(originalGraphCopy,
				String.format("graph_%s_originalCopied", _graphWriter._graphCounter));

		ArrayList<AnnotatedProgramPoint> procRootsToCheck = new ArrayList<AnnotatedProgramPoint>();

		// check for Ultimate.start -- assuming that if such a procedure exists,
		// it comes from the c translation
		for (AnnotatedProgramPoint procRoot : m_graphRoot.getOutgoingNodes()) {
			if (procRoot.getProgramPoint().getProcedure().startsWith("ULTIMATE.start")) {
				procRootsToCheck.add(procRoot);
				break;
			}
		}
		if (procRootsToCheck.isEmpty()) { // -> no Ultimate.start present
			// if (GlobalSettings._instance._checkOnlyMain) {
			// for (AnnotatedProgramPoint procRoot : m_graphRoot
			// .getOutgoingNodes()) {
			// if (procRoot.getProgramPoint().getProcedure()
			// .equalsIgnoreCase("main")) {
			// procRootsToCheck.add(procRoot);
			// break;
			// }
			// }
			// } else
			procRootsToCheck.addAll(m_graphRoot.getOutgoingNodes());
		}

		Result overallResult = Result.UNKNOWN;
		boolean allSafe = true;
		boolean verificationInterrupted = false;
		RcfgProgramExecution realErrorProgramExecution = null;
		
		//data collector variables
		int iterationsCount = 0;
		long startTime = System.nanoTime();
		BackwardCoveringInformation bwCoveringInfo = null;
		boolean weHaveSPWPInterpolation =  GlobalSettings._instance._solverAndInterpolator == SolverAndInterpolator.Z3SPWP;
		long noCBs = 0;
//		long[] soPreds = new long[] { 0L, 0L };
		long soPredsFP = 0;
		long soPredsBP = 0;
		long conjsInSSA = 0;
		long conjsInUC = 0;	

		TraceChecker traceChecker = null;

		for (AnnotatedProgramPoint procRoot : procRootsToCheck) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				verificationInterrupted = true;
				break;
			}

			mLogger.debug("Exploring : " + procRoot);
			AnnotatedProgramPoint procedureRoot = procRoot;

			IEmptinessCheck emptinessCheck = new NWAEmptinessCheck();

//			iterationsCount = 0;
			if (DEBUG)
				codeChecker.debug();
			while (loop_forever | iterationsCount++ < iterationsLimit) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					verificationInterrupted = true;
					break;
				}

				mLogger.debug(String.format("Iterations = %d\n", iterationsCount));
				NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun = emptinessCheck.checkForEmptiness(procedureRoot);

				if (errorRun == null) {
					_graphWriter.writeGraphAsImage(procedureRoot, String.format("graph_%s_%s_noEP",
							_graphWriter._graphCounter, procedureRoot.toString().substring(0, 5)));
					// if an error trace doesn't exist, return safe
					mLogger.warn("This Program is SAFE, Check terminated with " + iterationsCount + " iterations.");
					break;
				} else {
					mLogger.info("Error Path is FOUND.");
					_graphWriter.writeGraphAsImage(procedureRoot, String.format("graph_%s_%s_foundEP",
							_graphWriter._graphCounter, procedureRoot.toString().substring(0, 5)), errorRun
							.getStateSequence().toArray(new AnnotatedProgramPoint[] {}));
					
					if (GlobalSettings._instance._predicateUnification == PredicateUnification.PER_ITERATION)
						_predicateUnifier = new PredicateUnifier(mServices, m_smtManager);

					traceChecker = null;
					switch (GlobalSettings._instance._solverAndInterpolator) {
					case SMTINTERPOL:
						traceChecker = new TraceChecker(_predicateUnifier.getTruePredicate(),
							_predicateUnifier.getFalsePredicate(), // return LBool.UNSAT if trace
													// is infeasible
								new TreeMap<Integer, IPredicate>(), errorRun.getWord(), m_smtManager, m_originalRoot
										.getRootAnnot().getModGlobVarManager(),
								/*
								 * TODO : When Matthias introduced this
								 * parameter he set the argument to
								 * AssertCodeBlockOrder.NOT_INCREMENTALLY .
								 * Check if you want to set this to a different
								 * value.
								 */AssertCodeBlockOrder.NOT_INCREMENTALLY, mServices);
						break;
					case Z3SPWP:
						traceChecker = new TraceCheckerSpWp(_predicateUnifier.getTruePredicate(),
								_predicateUnifier.getFalsePredicate(), // return LBool.UNSAT if trace
								new TreeMap<Integer, IPredicate>(), // is
																	// infeasible
								errorRun.getWord(), m_smtManager, m_originalRoot.getRootAnnot().getModGlobVarManager(),
								/*
								 * TODO : When Matthias introduced this
								 * parameter he set the argument to
								 * AssertCodeBlockOrder.NOT_INCREMENTALLY .
								 * Check if you want to set this to a different
								 * value.
								 */
								AssertCodeBlockOrder.NOT_INCREMENTALLY,
								UnsatCores.CONJUNCT_LEVEL, true, mServices);
						break;
					}

					LBool isSafe = traceChecker.isCorrect();
					if (isSafe == LBool.UNSAT) { // trace is infeasible
//						if (GlobalSettings._instance._predicateUnification == PredicateUnification.PER_ITERATION)
//							_predicateUnifier = new PredicateUnifier(mServices, m_smtManager);//, m_truePredicate, m_falsePredicate);

						switch (GlobalSettings._instance._solverAndInterpolator) {
						case SMTINTERPOL:
							traceChecker.computeInterpolants(new TraceChecker.AllIntegers(), _predicateUnifier,
									GlobalSettings._instance._interpolationMode);
							break;
						case Z3SPWP:
							traceChecker.computeInterpolants(new TraceChecker.AllIntegers(), _predicateUnifier,
									INTERPOLATION.ForwardPredicates);
							break;
						}
						
						//interpolant coverage capability stuff
						ArrayList<ProgramPoint> programPoints = new ArrayList<>();
						for (AnnotatedProgramPoint app : errorRun.getStateSequence())
							programPoints.add(app.getProgramPoint());
						BackwardCoveringInformation bci = TraceCheckerUtils.computeCoverageCapability(traceChecker,
								programPoints, mLogger);
						if (bwCoveringInfo == null)
							bwCoveringInfo = bci;
						else
							bwCoveringInfo = new BackwardCoveringInformation(bwCoveringInfo, bci);
						noCBs += (Integer) traceChecker.getTraceCheckerBenchmark().getValue(s_NumberOfCodeBlocks);
						if (weHaveSPWPInterpolation) {
////							long[] curRes = (long[]) traceChecker.getTraceCheckerBenchmark().getValue(s_SizeOfPredicates);
//							long[] curRes = (long[]) traceChecker.getTraceCheckerBenchmark().getValue(s_SizeOfPredicatesFP);
//							for (int i = 0; i < 2; i++) {
//								soPreds[i] = soPreds[i] + curRes[i];
//							}
							soPredsFP += (Long) traceChecker.getTraceCheckerBenchmark().getValue(s_SizeOfPredicatesFP);
							soPredsBP += (Long) traceChecker.getTraceCheckerBenchmark().getValue(s_SizeOfPredicatesBP);
							conjsInSSA += (Integer) traceChecker.getTraceCheckerBenchmark().getValue(s_ConjunctsInSSA);
							conjsInUC += (Integer) traceChecker.getTraceCheckerBenchmark().getValue(s_ConjunctsInUnsatCore);	
						}
						

						IPredicate[] interpolants = traceChecker.getInterpolants();
						if (GlobalSettings._instance._memoizeNormalEdgeChecks
								&& GlobalSettings._instance._memoizeReturnEdgeChecks)
							codeChecker.codeCheck(errorRun, interpolants, procedureRoot, _satTriples, _unsatTriples,
									_satQuadruples, _unsatQuadruples);
						else if (GlobalSettings._instance._memoizeNormalEdgeChecks
								&& !GlobalSettings._instance._memoizeReturnEdgeChecks)
							codeChecker.codeCheck(errorRun, interpolants, procedureRoot, _satTriples, _unsatTriples);
						else
							codeChecker.codeCheck(errorRun, interpolants, procedureRoot);
					} else { // trace is feasible
						mLogger.warn("This program is UNSAFE, Check terminated with " + iterationsCount
								+ " iterations.");
						allSafe = false;
						traceChecker.computeRcfgProgramExecution();
						realErrorProgramExecution = traceChecker.getRcfgProgramExecution();

						if (DEBUG)
							codeChecker.debug();
						break;
					}
				}
				if (DEBUG)
					codeChecker.debug();
			}
			m_graphRoot = copyGraph(originalGraphCopy);
			codeChecker.m_graphRoot = m_graphRoot;

			if (!allSafe)
				break;
		}

		if (DEBUG)
			codeChecker.debug();

		if (!verificationInterrupted) {
			if (allSafe)
				overallResult = Result.CORRECT;
			else
				overallResult = Result.INCORRECT;
		} else {
			reportTimoutResult(mErrNodesOfAllProc);
		}

		mLogger.debug("MemoizationHitsSat: " + codeChecker.memoizationHitsSat);
		mLogger.debug("MemoizationHitsUnsat: " + codeChecker.memoizationHitsUnsat);
		mLogger.debug("MemoizationReturnHitsSat: " + codeChecker.memoizationReturnHitsSat);
		mLogger.debug("MemoizationReturnHitsUnsat: " + codeChecker.memoizationReturnHitsUnsat);
		
		//inserted by alex: we should return this kind of benchmark result
		
//		CodeCheckBenchmarks ccb = new CodeCheckBenchmarks(traceChecker instanceof TraceCheckerSpWp);
		CodeCheckBenchmarks ccb = new CodeCheckBenchmarks();
		ICsvProvider<Object> ccbcsvp = ccb.createCvsProvider();
		ArrayList<Object> values = new ArrayList<>();
		values.add((int) ((System.nanoTime() - startTime)/1000000));
		values.add(iterationsCount);

		values.add(noCBs);
		if (weHaveSPWPInterpolation) {
			values.add(soPredsFP);
			values.add(soPredsBP);
			values.add(conjsInSSA);
			values.add(conjsInUC);
		} else {
			values.add(-1);
			values.add(-1);
			values.add(-1);
			values.add(-1);
		}

		values.add(bwCoveringInfo);
		values.add(((double) bwCoveringInfo.getSuccessfullBackwardCoverings())
				/bwCoveringInfo.getPotentialBackwardCoverings());
		ccbcsvp.addRow(values);
		reportBenchmark(ccb);

		if (overallResult == Result.CORRECT) {
			reportPositiveResults(mErrNodesOfAllProc);
		} else if (overallResult == Result.INCORRECT) {
			reportCounterexampleResult(realErrorProgramExecution);
		} else {
			String shortDescription = "Unable to decide if program is safe!";
			String longDescription = "Unable to decide if program is safe!";
			GenericResult result = new GenericResult(Activator.s_PLUGIN_NAME, shortDescription, longDescription,
					Severity.INFO);
			mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, result);
		}

		return false;
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
		BenchmarkResult<T> res = new BenchmarkResult<T>(Activator.s_PLUGIN_NAME, shortDescription, benchmark);
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
				PositiveResult<RcfgElement> pResult = new PositiveResult<RcfgElement>(Activator.s_PLUGIN_NAME,
						errorLoc, mServices.getBacktranslationService());
				reportResult(pResult);
			}
		}
		AllSpecificationsHoldResult result = new AllSpecificationsHoldResult(Activator.s_PLUGIN_NAME, longDescription);
		reportResult(result);
		mLogger.info(result.getShortDescription() + " " + result.getLongDescription());
	}

	private void reportCounterexampleResult(RcfgProgramExecution pe) {
		if (pe.isOverapproximation()) {
			reportUnproveableResult(pe);
			return;
		}

		reportResult(new CounterExampleResult<RcfgElement,CodeBlock, Expression>(getErrorPP(pe), Activator.s_PLUGIN_NAME,
				mServices.getBacktranslationService(), pe));
	}

	private void reportUnproveableResult(RcfgProgramExecution pe) {
		ProgramPoint errorPP = getErrorPP(pe);
		UnprovableResult<RcfgElement, CodeBlock, Expression> uknRes = new UnprovableResult<RcfgElement, CodeBlock, Expression>(
				Activator.s_PLUGIN_NAME, errorPP, mServices.getBacktranslationService(), pe);
		reportResult(uknRes);
	}

	public ProgramPoint getErrorPP(RcfgProgramExecution rcfgProgramExecution) {
		int lastPosition = rcfgProgramExecution.getLength() - 1;
		CodeBlock last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}
	
	private void reportTimoutResult(Collection<ProgramPoint> errorLocs) {
		for (ProgramPoint errorLoc : errorLocs) {
			ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage = "Unable to prove that "
					+ ResultUtil.getCheckedSpecification(errorLoc).getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			TimeoutResultAtElement<RcfgElement> timeOutRes = new TimeoutResultAtElement<RcfgElement>(errorLoc,
					Activator.s_PLUGIN_NAME, mServices.getBacktranslationService(),
					timeOutMessage);
			reportResult(timeOutRes);
			// s_Logger.warn(timeOutMessage);
		}
	}

	// private void reportCounterexampleResult(CodeBlock position,
	// List<ILocation> failurePath,
	// IProgramExecution<RcfgElement, Expression> pe) {
	// ILocation errorLoc = failurePath.get(failurePath.size() - 1);
	// ILocation origin = errorLoc.getOrigin();
	//
	// List<ITranslator<?, ?, ?, ?>> translatorSequence = UltimateServices
	// .getInstance().getTranslatorSequence();
	// String ctxMessage = origin.checkedSpecification().getNegativeMessage();
	// ctxMessage += " (line " + origin.getStartLine() + ")";
	// Backtranslator backtrans = (Backtranslator) translatorSequence
	// .get(translatorSequence.size() - 1);
	// BoogieProgramExecution bpe = (BoogieProgramExecution) backtrans
	// .translateProgramExecution(pe);
	// CounterExampleResult<RcfgElement, Expression> ctxRes = new
	// CounterExampleResult<RcfgElement, Expression>(
	// position, Activator.s_PLUGIN_NAME, translatorSequence, pe,
	// CounterExampleResult.getLocationSequence(bpe),
	// bpe.getValuation());
	// ctxRes.setLongDescription(bpe.toString());
	//
	// System.out.println("=== Start of program execution");
	// System.out.println("--- Error Path: ---");
	// for (ILocation loc : ctxRes.getFailurePath()) {
	// System.out.println(loc.toString());
	// }
	// System.out.println("--- Valuation: ---");
	// System.out.println(bpe.toString());
	// System.out.println("=== End of program execution");
	//
	// reportResult(ctxRes);
	// s_Logger.warn(ctxMessage);
	// }

	private void reportResult(IResult res) {
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, res);
	}

	// Debug

	public ImpRootNode getRoot() {
		return codeChecker.m_graphRoot;
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}
}