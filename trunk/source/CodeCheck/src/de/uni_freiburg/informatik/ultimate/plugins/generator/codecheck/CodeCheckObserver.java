package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues.SolverAndInterpolator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Backtranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.AnnotateAndAsserter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

import org.apache.log4j.Logger;


/**
 * Auto-Generated Stub for the plug-in's Observer
 */

enum Checker { ULTIMATE, IMPULSE }
enum Result { CORRECT, TIMEOUT , MAXEDITERATIONS , UNKNOWN , INCORRECT }


public class CodeCheckObserver implements IUnmanagedObserver {

	public static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private CodeChecker codeChecker;
	
	RootNode m_originalRoot;
	TAPreferences m_taPrefs;
	ImpRootNode m_graphRoot;
	
	SmtManager m_smtManager;
	IPredicate m_truePredicate;
	IPredicate m_falsePredicate;
	PredicateUnifier _predicateUnifier;
	EdgeChecker m_edgeChecker;
	
	GraphWriter _graphWriter;

	HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> _satTriples;
	HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> _unsatTriples;
	HashMap<IPredicate, HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>> _satQuadruples;
	HashMap<IPredicate, HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>> _unsatQuadruples;
	
	private static final boolean DEBUG = false;

	/**
	 * Initialize all the required objects in the implementation.
	 * @param root
	 * @return
	 */
	public boolean initialize(IElement root) {
		readPreferencePage();
		
		m_originalRoot = (RootNode) root;
		RootAnnot rootAnnot = m_originalRoot.getRootAnnot();
		m_taPrefs = rootAnnot.getTaPrefs();
		m_smtManager = new SmtManager(rootAnnot.getBoogie2SMT(),
				Solver.SMTInterpol, rootAnnot.getGlobalVars(),
				rootAnnot.getModGlobVarManager(), false, "");

		m_truePredicate = m_smtManager.newTruePredicate();
		m_falsePredicate = m_smtManager.newFalsePredicate();
		
		_predicateUnifier = new PredicateUnifier(m_smtManager, m_truePredicate, m_falsePredicate);
		m_edgeChecker = new EdgeChecker(m_smtManager, rootAnnot.getModGlobVarManager());
		
		if (GlobalSettings._instance._memoizeNormalEdgeChecks) {
			_satTriples = new HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>();
			_unsatTriples = new HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>();
		}
		if (GlobalSettings._instance._memoizeReturnEdgeChecks) {
			_satQuadruples = new HashMap<IPredicate, HashMap<IPredicate,HashMap<CodeBlock,HashSet<IPredicate>>>>();
			_unsatQuadruples = new HashMap<IPredicate, HashMap<IPredicate,HashMap<CodeBlock,HashSet<IPredicate>>>>();
		}
		_graphWriter = new GraphWriter(GlobalSettings._instance._dotGraphPath, 
				true, true, true, false, m_smtManager.getScript());
		
	
		RCFG2AnnotatedRCFG r2ar = new RCFG2AnnotatedRCFG(m_smtManager);
		m_graphRoot = r2ar.convert(m_originalRoot, m_truePredicate);
		
		_graphWriter.writeGraphAsImage(m_graphRoot,
				String.format("graph_%s_originalAfterConversion", _graphWriter._graphCounter));
		
		removeSummaryEdges();
		
		_graphWriter.writeGraphAsImage(m_graphRoot,
				String.format("graph_%s_originalSummaryEdgesRemoved", _graphWriter._graphCounter));
	
		if (GlobalSettings._instance.checker == Checker.IMPULSE) {
			codeChecker = new ImpulseChecker(
					root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs, 
					m_originalRoot, m_graphRoot, _graphWriter, m_edgeChecker, _predicateUnifier);
		} else {
			codeChecker = new UltimateChecker(
					root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs, 
					m_originalRoot, m_graphRoot, _graphWriter, m_edgeChecker, _predicateUnifier);
		}
		return false;
	}

	private void readPreferencePage() {
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		
		GlobalSettings.init();
		
		GlobalSettings._instance._memoizeNormalEdgeChecks = prefs.getBoolean(PreferenceValues.NAME_MEMOIZENORMALEDGECHECKS, 
				PreferenceValues.DEF_MEMOIZENORMALEDGECHECKS);
		GlobalSettings._instance._memoizeReturnEdgeChecks = prefs.getBoolean(PreferenceValues.NAME_MEMOIZERETURNEDGECHECKS, 
				PreferenceValues.DEF_MEMOIZERETURNEDGECHECKS);
		GlobalSettings._instance._checkOnlyMain = prefs.getBoolean(PreferenceValues.NAME_ONLYMAINPROCEDURE, 
				PreferenceValues.DEF_ONLYMAINPROCEDURE);
				
		String solverString = prefs.getString(PreferenceValues.NAME_SOLVERANDINTERPOLATOR, 
				PreferenceValues.DEF_SOLVERANDINTERPOLATOR.toString());
		if (solverString.equals(PreferenceValues.VALUE_SOLVERANDINTERPOLATOR_SMTINTERPOL.toString()))
			GlobalSettings._instance._solverAndInterpolator = SolverAndInterpolator.SMTINTERPOL;
		else if (solverString.equals(PreferenceValues.VALUE_SOLVERANDINTERPOLATOR_Z3SPWP.toString()))
			GlobalSettings._instance._solverAndInterpolator = SolverAndInterpolator.Z3SPWP;
		
		String interpolationModeString = prefs.getString(PreferenceValues.NAME_INTERPOLATIONMODE,
				PreferenceValues.DEF_INTERPOLATIONMODE.toString());
		if (interpolationModeString.equals(PreferenceValues.VALUE_INTERPOLATIONMODE_TREE.toString()))
			GlobalSettings._instance._interpolationMode = INTERPOLATION.Craig_TreeInterpolation;
		else if (interpolationModeString.equals(PreferenceValues.VALUE_INTERPOLATIONMODE_NESTED.toString()))
			GlobalSettings._instance._interpolationMode = INTERPOLATION.Craig_NestedInterpolation;
		
		String predicateUnificationString = prefs.getString(PreferenceValues.NAME_PREDICATEUNIFICATION, 
				PreferenceValues.DEF_PREDICATEUNIFICATION.toString());
		if (predicateUnificationString.equals(PreferenceValues.VALUE_PREDICATEUNIFICATION_PERVERIFICATION.toString()))
			GlobalSettings._instance._predicateUnification = PredicateUnification.PER_VERIFICATION;
		else if (predicateUnificationString.equals(PreferenceValues.VALUE_PREDICATEUNIFICATION_PERITERATION.toString()))
			GlobalSettings._instance._predicateUnification = PredicateUnification.PER_ITERATION;
		else if (predicateUnificationString.equals(PreferenceValues.VALUE_PREDICATEUNIFICATION_NONE.toString()))
			GlobalSettings._instance._predicateUnification = PredicateUnification.NONE;
		
		String edgeCheckOptimizationString = prefs.getString(PreferenceValues.NAME_EDGECHECKOPTIMIZATION, 
				PreferenceValues.DEF_EDGECHECKOPTIMIZATION.toString());
		if (edgeCheckOptimizationString.equals(PreferenceValues.VALUE_EDGECHECKOPTIMIZATION_NONE.toString()))
			GlobalSettings._instance._edgeCheckOptimization = EdgeCheckOptimization.NONE;
		else if (edgeCheckOptimizationString.equals(PreferenceValues.VALUE_EDGECHECKOPTIMIZATION_SDEC.toString()))
			GlobalSettings._instance._edgeCheckOptimization = EdgeCheckOptimization.SDEC;
		else if (edgeCheckOptimizationString.equals(PreferenceValues.VALUE_EDGECHECKOPTIMIZATION_PUSHPOP.toString()))
			GlobalSettings._instance._edgeCheckOptimization = EdgeCheckOptimization.PUSHPOP;
		else if (edgeCheckOptimizationString.equals(PreferenceValues.VALUE_EDGECHECKOPTIMIZATION_PUSHPOPSDEC.toString()))
			GlobalSettings._instance._edgeCheckOptimization = EdgeCheckOptimization.PUSHPOP_SDEC;
	}
	
	private void removeSummaryEdges() {
		Stack <AnnotatedProgramPoint> stack = new Stack<AnnotatedProgramPoint>();
		HashSet<AnnotatedProgramPoint> visited = new HashSet<AnnotatedProgramPoint>();
		visited.add(m_graphRoot);
		stack.add(m_graphRoot);
		while(!stack.isEmpty()) {
			AnnotatedProgramPoint node = stack.pop();
			AppEdge[] outEdges = node.getOutgoingEdges().toArray(new AppEdge[]{});
			for (AppEdge outEdge : outEdges) {
				AnnotatedProgramPoint successor = outEdge.getTarget();
				if (outEdge.getStatement() instanceof Summary) {
					if (((Summary) outEdge.getStatement()).calledProcedureHasImplementation())
						outEdge.disconnect();
				}
				if(!visited.contains(successor)) {
					visited.add(successor);
					stack.add(successor);
				}
			}
		}
	}
	
	public boolean process(IElement root) {
		initialize(root);
		
		final boolean loop_forever = true; // for DEBUG
		final int iterationsLimit = 0; // for DEBUG
		
		_graphWriter.writeGraphAsImage(m_graphRoot,
				String.format("graph_%s_original", _graphWriter._graphCounter));
		
		ImpRootNode originalGraphCopy = copyGraph(m_graphRoot);
		
		_graphWriter.writeGraphAsImage(originalGraphCopy, 
				String.format("graph_%s_originalCopied", _graphWriter._graphCounter));

		ArrayList<AnnotatedProgramPoint> procRootsToCheck = new ArrayList<AnnotatedProgramPoint>();
		if (GlobalSettings._instance.svcomp2014Mode) {
			for (AnnotatedProgramPoint procRoot : m_graphRoot.getOutgoingNodes()) {
				if (procRoot.getProgramPoint().getProcedure().startsWith("ULTIMATE.start")) {
					procRootsToCheck.add(procRoot);
					break;
				}
			}	
		} else if (GlobalSettings._instance._checkOnlyMain) {
			for (AnnotatedProgramPoint procRoot : m_graphRoot.getOutgoingNodes()) {
				if (procRoot.getProgramPoint().getProcedure().equalsIgnoreCase("main")) {
					procRootsToCheck.add(procRoot);
					break;
				}
			}
		}
		else
			procRootsToCheck.addAll(m_graphRoot.getOutgoingNodes());
		
		Result overallResult = Result.UNKNOWN;
		boolean allSafe = true;
		boolean verificationInterrupted = false;
		NestedRun<CodeBlock, AnnotatedProgramPoint> realErrorRun = null;
		RcfgProgramExecution realErrorProgramExecution = null;
		List<CodeBlock> realErrorFailurePath = null;
		
		for (AnnotatedProgramPoint procRoot : procRootsToCheck) {
			if (!UltimateServices.getInstance().continueProcessing()) {
				verificationInterrupted = true;
				break;
			}
			
			s_Logger.debug("Exploring : " + procRoot);
			AnnotatedProgramPoint procedureRoot = procRoot;
			
			//FIXME
//			IEmptinessCheck emptinessCheck = new BFSEmptinessCheck();
			IEmptinessCheck emptinessCheck = new NWAEmptinessCheck();
			
			int iterationsCount = 0; // for DEBUG
			if (DEBUG)
				codeChecker.debug();
			while (loop_forever | iterationsCount++ < iterationsLimit) {
				if (!UltimateServices.getInstance().continueProcessing()) {
					verificationInterrupted = true;
					break;
				}
				
				s_Logger.debug(String.format("Iterations = %d\n", iterationsCount));
				NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun = 
						emptinessCheck.checkForEmptiness(procedureRoot);
				
				if (errorRun == null) {
					_graphWriter.writeGraphAsImage(procedureRoot, 
						String.format("graph_%s_%s_noEP", _graphWriter._graphCounter, procedureRoot.toString().substring(0, 5)));
					// if an error trace doesn't exist, return safe
					s_Logger.info("This Program is SAFE, Check terminated with " + iterationsCount + " iterations.");
					break;
				} else {
					s_Logger.info("Error Path is FOUND.");
					_graphWriter.writeGraphAsImage(procedureRoot, 
						String.format("graph_%s_%s_foundEP", _graphWriter._graphCounter, procedureRoot.toString().substring(0, 5)), 
						errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[]{}));
					
					TraceChecker traceChecker = null;
					switch (GlobalSettings._instance._solverAndInterpolator) {
					case SMTINTERPOL :
						traceChecker = new TraceChecker(
								m_truePredicate, // checks whether the trace is feasible, i.e. the formula is satisfiable
								m_falsePredicate,  //return LBool.UNSAT if trace is infeasible
								null,
								errorRun.getWord(),
								m_smtManager, 
								m_originalRoot.getRootAnnot().getModGlobVarManager());
						break;
					case Z3SPWP :
						traceChecker = new TraceCheckerSpWp(
								m_truePredicate, // checks whether the trace is feasible, i.e. the formula is satisfiable
								m_falsePredicate,  //return LBool.UNSAT if trace is infeasible
								errorRun.getWord(),
								m_smtManager, 
								m_originalRoot.getRootAnnot().getModGlobVarManager());
						break;
					}
					


					LBool isSafe = traceChecker.isCorrect();
					if(isSafe == LBool.UNSAT) { //trace is infeasible
						if (GlobalSettings._instance._predicateUnification == PredicateUnification.PER_ITERATION) 
							_predicateUnifier = new PredicateUnifier(m_smtManager, m_truePredicate, m_falsePredicate);
						
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
						
						IPredicate[] interpolants = traceChecker.getInterpolants();
						if (GlobalSettings._instance._memoizeNormalEdgeChecks 
								&& GlobalSettings._instance._memoizeReturnEdgeChecks)
							codeChecker.codeCheck(errorRun, interpolants, procedureRoot, 
									_satTriples, _unsatTriples, _satQuadruples, _unsatQuadruples);
						else if (GlobalSettings._instance._memoizeNormalEdgeChecks 
								&& !GlobalSettings._instance._memoizeReturnEdgeChecks)
							codeChecker.codeCheck(errorRun, interpolants, procedureRoot, _satTriples, _unsatTriples);
						else
							codeChecker.codeCheck(errorRun, interpolants, procedureRoot);
					} else { // trace is feasible
						s_Logger.info("This program is UNSAFE, Check terminated with " + iterationsCount + " iterations.");
						allSafe = false;
						realErrorRun = errorRun;
						realErrorProgramExecution = traceChecker.getRcfgProgramExecution();
						realErrorFailurePath = traceChecker.getFailurePath();
						
						if (DEBUG)
							codeChecker.debug();
						break;
					}
				}
				if(DEBUG)
					codeChecker.debug();
			}
			m_graphRoot = copyGraph(originalGraphCopy);
			codeChecker.m_graphRoot = m_graphRoot;
			
			if (!allSafe)
				break;
		}

		if(DEBUG)
			codeChecker.debug();
		
		if (!verificationInterrupted)
			if (allSafe)
				overallResult = Result.CORRECT;
			else
				overallResult = Result.INCORRECT;
		
		
		s_Logger.info("-----------------");
		s_Logger.info(overallResult);
		s_Logger.info("-----------------");

		s_Logger.info("PC#: " + m_smtManager.getInterpolQueries());
		s_Logger.info("TIME#: " + m_smtManager.getInterpolQuriesTime());
		s_Logger.info("ManipulationTIME#: " + m_smtManager.getTraceCheckTime());
		s_Logger.info("EC#: " + m_smtManager.getNontrivialSatQueries());
		s_Logger.info("TIME#: " + m_smtManager.getSatCheckTime());
//		s_Logger.info("ManipulationTIME#: "	+ m_smtManager.getCodeBlockCheckTime());
		s_Logger.info("MemoizationHitsSat: " + codeChecker.memoizationHitsSat);
		s_Logger.info("MemoizationHitsUnsat: " + codeChecker.memoizationHitsUnsat);
		s_Logger.info("MemoizationReturnHitsSat: " + codeChecker.memoizationReturnHitsSat);
		s_Logger.info("MemoizationReturnHitsUnsat: " + codeChecker.memoizationReturnHitsUnsat);
		
		if (overallResult == Result.CORRECT) {
			PositiveResult<CodeBlock> result = new PositiveResult<CodeBlock>(
					null,
					Activator.s_PLUGIN_NAME,
					UltimateServices.getInstance().getTranslatorSequence(),
					this.m_graphRoot.getPayload().getLocation());
			result.setShortDescription("Program is safe!");
			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, result);
//			reportResult(result);
		} else if (overallResult == Result.INCORRECT) {
			reportCounterexampleResult(realErrorRun.getWord().getSymbol(realErrorRun.getWord().length() - 1),
					AbstractCegarLoop.trace2path(realErrorFailurePath) , realErrorProgramExecution);
		} else {
			UnprovableResult<CodeBlock> result = new UnprovableResult<CodeBlock>(null,
					Activator.s_PLUGIN_NAME,
					UltimateServices.getInstance().getTranslatorSequence(),
					null);
			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, result);
		}
		
		return false;
	}
	
	/**
	 * Given a graph root, copy all the nodes and the corresponding connections.
	 * @param root
	 * @return
	 */
	public ImpRootNode copyGraph(ImpRootNode root) {
		HashMap <AnnotatedProgramPoint, AnnotatedProgramPoint> copy = new HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint>();
		ImpRootNode newRoot = new ImpRootNode(root.getRootAnnot());
		copy.put(root, newRoot);
		Stack <AnnotatedProgramPoint> stack = new Stack<AnnotatedProgramPoint>();
		for (AnnotatedProgramPoint child : root.getOutgoingNodes()) {
			stack.add(child);
		}
		while (!stack.isEmpty()) {
			AnnotatedProgramPoint current = stack.pop();
			if (copy.containsKey(current))
				continue;
			copy.put(current, new AnnotatedProgramPoint(current));
			List <AnnotatedProgramPoint> nextNodes = current.getOutgoingNodes();
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
						newNode.connectOutgoingReturn(hier,
								(Return) outHypEdge.getStatement(), copy.get(outHypEdge.getTarget()));
				} else {
					newNode.connectOutgoing(outEdge.getStatement(), copy.get(outEdge.getTarget()));
				}
			}
		}
		return newRoot;
	}

	private void reportCounterexampleResult(CodeBlock position, List<ILocation> failurePath, 
			IProgramExecution<RcfgElement, Expression> pe) {
		ILocation errorLoc = failurePath.get(failurePath.size()-1);
		ILocation origin = errorLoc.getOrigin();
		
		List<ITranslator<?, ?, ?, ?>> translatorSequence = UltimateServices.getInstance().getTranslatorSequence();
		CounterExampleResult<RcfgElement> ctxRes = new CounterExampleResult<RcfgElement>(
				position,
				Activator.s_PLUGIN_NAME,
				translatorSequence,
				origin, null);
		String ctxMessage = origin.checkedSpecification().getNegativeMessage();
		ctxRes.setShortDescription(ctxMessage);		
		ctxMessage += " (line " + origin.getStartLine() + ")";
		Backtranslator backtrans = (Backtranslator) translatorSequence.get(translatorSequence.size()-1);
		BoogieProgramExecution bpe = (BoogieProgramExecution) backtrans.translateProgramExecution(pe);
		ctxRes.setLongDescription(bpe.toString());
		ctxRes.setFailurePath(bpe.getLocationSequence());
		ctxRes.setValuation(bpe.getValuation());
		reportResult(ctxRes);
		s_Logger.warn(ctxMessage);
	}
	
	private void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
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