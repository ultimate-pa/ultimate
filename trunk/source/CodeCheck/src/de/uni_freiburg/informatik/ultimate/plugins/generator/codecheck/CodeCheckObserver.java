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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AbstractInterpretationPredicates;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.SolverAndInterpolator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.emptinesscheck.IEmptinessCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.emptinesscheck.NWAEmptinessCheck;
//import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.ImpulsChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.ImpulseChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.kojak.UltimateChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.ResultUtil;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
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

	public final Logger mLogger;
	private CodeChecker codeChecker;

	RootNode m_originalRoot;
	TAPreferences m_taPrefs;
	ImpRootNode m_graphRoot;

	SmtManager m_smtManager;
	public PredicateUnifier _predicateUnifier;
	IHoareTripleChecker m_edgeChecker;

	GraphWriter _graphWriter;

	NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> _satTriples;
	NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> _unsatTriples;
	NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> _satQuadruples;
	NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> _unsatQuadruples;
	Collection<ProgramPoint> mErrNodesOfAllProc;
	private final IUltimateServiceProvider mServices;

	private static final boolean DEBUG = false;
	

	boolean loop_forever = true; // for DEBUG
	int iterationsLimit = -1; // for DEBUG
	private boolean outputHoareAnnotation = true;


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
		m_smtManager = new SmtManager(rootAnnot.getScript(), rootAnnot.getBoogie2SMT(), rootAnnot.getModGlobVarManager(), mServices, false);

		_predicateUnifier = new PredicateUnifier(mServices, m_smtManager);

		m_edgeChecker = new MonolithicHoareTripleChecker(m_smtManager);

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
				m_smtManager.getScript());

		boolean usePredicatesFromAbstractInterpretation = true; //TODO make a Pref
		Map<RCFGNode, Term> initialPredicates = null;
		if (usePredicatesFromAbstractInterpretation)  {
			try {
				initialPredicates = AbstractInterpretationPredicates.getAnnotation(m_originalRoot).getPredicates();
			} catch (NullPointerException npe) {
				mLogger.warn("was not able to retrieve initial predicates from abstract interpretation --> wrong toolchain?? (using \"true\")");
				initialPredicates = null;
			}
		}
		RCFG2AnnotatedRCFG r2ar = new RCFG2AnnotatedRCFG(m_smtManager, mLogger, _predicateUnifier.getTruePredicate(), initialPredicates);
		m_graphRoot = r2ar.convert(mServices, m_originalRoot);

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

		GlobalSettings._instance.redirectionStrategy = prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_REDIRECTION, RedirectionStrategy.class);

		GlobalSettings._instance.defaultRedirection = prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_DEF_RED, CodeCheckPreferenceInitializer.DEF_DEF_RED);
		GlobalSettings._instance.removeFalseNodes = prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_RM_FALSE, CodeCheckPreferenceInitializer.DEF_RM_FALSE);
		GlobalSettings._instance.checkSatisfiability = prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_CHK_SAT, CodeCheckPreferenceInitializer.DEF_CHK_SAT);
	
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
			procRootsToCheck.addAll(m_graphRoot.getOutgoingNodes());
		}

		Result overallResult = Result.UNKNOWN;
		boolean allSafe = true;
		boolean verificationInterrupted = false;
		RcfgProgramExecution realErrorProgramExecution = null;
		
		//benchmark data collector variables
		int iterationsCount = 0;
		long startTime = System.nanoTime();
		BackwardCoveringInformation bwCoveringInfo = null;
		boolean weHaveSPWPInterpolation =  GlobalSettings._instance._solverAndInterpolator == SolverAndInterpolator.Z3SPWP;
		long noCBs = 0;
		long soPredsFP = 0;
		long soPredsBP = 0;
		long conjsInSSA = 0;
		long conjsInUC = 0;	

		InterpolatingTraceChecker traceChecker = null;

		for (AnnotatedProgramPoint procedureRoot : procRootsToCheck) {
//		for (AnnotatedProgramPoint procRoot : procRootsToCheck) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				verificationInterrupted = true;
				break;
			}

			mLogger.debug("Exploring : " + procedureRoot);
			//mLogger.debug("Exploring : " + procRoot);
			//AnnotatedProgramPoint procedureRoot = procRoot;

			IEmptinessCheck emptinessCheck = new NWAEmptinessCheck(mServices);

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
					//TODO: this only works for the case where we have 1 procedure in procRootsToCheck, right??
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
						traceChecker = new InterpolatingTraceCheckerCraig(_predicateUnifier.getTruePredicate(),
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
								 */AssertCodeBlockOrder.NOT_INCREMENTALLY, mServices, true, _predicateUnifier,
									GlobalSettings._instance._interpolationMode);
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
								UnsatCores.CONJUNCT_LEVEL, true, mServices, true, _predicateUnifier,
								GlobalSettings._instance._interpolationMode, m_smtManager);
						break;
					}
					if (traceChecker.getToolchainCancelledExpection() != null) {
						throw traceChecker.getToolchainCancelledExpection();
					}

					LBool isSafe = traceChecker.isCorrect();
					if (isSafe == LBool.UNSAT) { // trace is infeasible
						
						//interpolant coverage capability stuff
						ArrayList<ProgramPoint> programPoints = new ArrayList<>();
						for (AnnotatedProgramPoint app : errorRun.getStateSequence())
							programPoints.add(app.getProgramPoint());
						BackwardCoveringInformation bci = TraceCheckerUtils.computeCoverageCapability(mServices, traceChecker,
								programPoints, mLogger);
						if (bwCoveringInfo == null)
							bwCoveringInfo = bci;
						else
							bwCoveringInfo = new BackwardCoveringInformation(bwCoveringInfo, bci);
						noCBs += (Integer) traceChecker.getTraceCheckerBenchmark().getValue(s_NumberOfCodeBlocks);
						if (weHaveSPWPInterpolation) {
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
			reportTimeoutResult(mErrNodesOfAllProc);
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

		if (bwCoveringInfo != null) {
			values.add(bwCoveringInfo);
			if (bwCoveringInfo.getPotentialBackwardCoverings() != 0) {
				values.add(((double) bwCoveringInfo.getSuccessfullBackwardCoverings())
					/bwCoveringInfo.getPotentialBackwardCoverings());
			} else {
				values.add(1d);
			}
			ccbcsvp.addRow(values);
		} else {
			values.add(-1);
			values.add(-1);
		}
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
			GenericResult result = new GenericResult(Activator.s_PLUGIN_NAME, shortDescription, longDescription,
					Severity.INFO);
			mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, result);
		}

		return false;
	}

	//taken from TraceAbstractionStarter
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

	private HashMap<ProgramPoint,Term> computeHoareAnnotation(AnnotatedProgramPoint pr) {
		HashMap<ProgramPoint, HashSet<AnnotatedProgramPoint>> programPointToAnnotatedProgramPoints = new HashMap<>();

		HashMap<ProgramPoint, Term> programPointToHoareAnnotation = new HashMap<>();

		computeProgramPointToAnnotatedProgramPoints(pr, programPointToAnnotatedProgramPoints); 
		
		for (Entry<ProgramPoint, HashSet<AnnotatedProgramPoint>> kvp : programPointToAnnotatedProgramPoints.entrySet()) {
			IPredicate annot = m_smtManager.newFalsePredicate();

			for (AnnotatedProgramPoint app : kvp.getValue()) {
				TermVarsProc tvp = m_smtManager.or(annot, app.getPredicate());
				annot = m_smtManager.newSPredicate(kvp.getKey(), tvp);
			}
	//		programPointToHoareAnnotation.put(kvp.getKey(), annot.getClosedFormula());
			programPointToHoareAnnotation.put(kvp.getKey(), annot.getFormula());
		}
		return programPointToHoareAnnotation;
	}

	/**
	 * fill up the map programPointToAnnotatedProgramPoints with the reachable part of the CFG
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
				if (!visited.contains(outEdge.getTarget())){
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
		if (!pe.getOverapproximations().isEmpty()) {
			reportUnproveableResult(pe, pe.getUnprovabilityReasons());
			return;
		}

		reportResult(new CounterExampleResult<RcfgElement,CodeBlock, Expression>(getErrorPP(pe), Activator.s_PLUGIN_NAME,
				mServices.getBacktranslationService(), pe));
	}

	private void reportUnproveableResult(RcfgProgramExecution pe, List<UnprovabilityReason> unproabilityReasons) {
		ProgramPoint errorPP = getErrorPP(pe);
		UnprovableResult<RcfgElement, CodeBlock, Expression> uknRes = new UnprovableResult<RcfgElement, CodeBlock, Expression>(
				Activator.s_PLUGIN_NAME, errorPP, mServices.getBacktranslationService(), pe, unproabilityReasons);
		reportResult(uknRes);
	}

	public ProgramPoint getErrorPP(RcfgProgramExecution rcfgProgramExecution) {
		int lastPosition = rcfgProgramExecution.getLength() - 1;
		CodeBlock last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}
	
	private void reportTimeoutResult(Collection<ProgramPoint> errorLocs) {
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
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}
}
