package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Stack;


import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Backtranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.AnnotateAndAsserter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

import org.apache.log4j.Logger;


/**
 * Auto-Generated Stub for the plug-in's Observer
 */

enum Checker {
	ULTIMATE, IMPULSE
}

enum Result { CORRECT, TIMEOUT , MAXEDITERATIONS , UNKNOWN , INCORRECT }

public class CodeCheckObserver implements IUnmanagedObserver {

	private Checker checker;
	public static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private CodeChecker codeChecker;
	
	public RootNode m_originalRoot;
	public TAPreferences m_taPrefs;
	
	public SmtManager m_smtManager;
	public IPredicate m_truePredicate;
	public IPredicate m_falsePredicate;
	
	GraphWriter m_graphWriter;
	String m_dotGraphPath = "C:/temp/codeCheckGraphs";
	
	public ImpRootNode m_graphRoot;

	private static final boolean DEBUG = false;
	
	private PrintWriter dumpInitialize() { // copied from Impulse, needed for trace checker
		File file = 
				new File(m_taPrefs.dumpPath() + "/" + ".txt");
		FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(file);
			return new PrintWriter(fileWriter);
		} catch (IOException e) {
			e.printStackTrace();
		} 
		return null;
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
					newNode.connectOutgoingReturn(copy.get(outHypEdge.getTarget()), 
							copy.get(outHypEdge.getHier()), (Return) outHypEdge.getStatement());
				} else {
					newNode.connectOutgoing(copy.get(outEdge.getTarget()), outEdge.getStatement());
				}
			}
		}
		return newRoot;
	}
	
	/**
	 * Initialize all the required objects in the implementation.
	 * @param root
	 * @return
	 */
	public boolean initialize(IElement root) {
		m_originalRoot = (RootNode) root;
		RootAnnot rootAnnot = m_originalRoot.getRootAnnot();
		m_taPrefs = rootAnnot.getTaPrefs();
		m_smtManager = new SmtManager(rootAnnot.getBoogie2SMT(),
				Solver.SMTInterpol, rootAnnot.getGlobalVars(),
				rootAnnot.getModGlobVarManager(), false, "");

		m_truePredicate = m_smtManager.newTruePredicate();
		m_falsePredicate = m_smtManager.newFalsePredicate();
		
		m_graphWriter = new GraphWriter(m_dotGraphPath, 
				true, true, true, false, m_smtManager.getScript());
		
		RCFG2AnnotatedRCFG r2ar = new RCFG2AnnotatedRCFG(m_smtManager);
		m_graphRoot = r2ar.convert(m_originalRoot, m_truePredicate);
		removeSummaryEdges();
		if (checker == Checker.IMPULSE) {
			codeChecker = new ImpulseChecker(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot, m_graphWriter);
		} else {
			codeChecker = new UltimateChecker(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs, m_originalRoot, m_graphRoot, m_graphWriter);
		}
		return false;
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
		//FIXME
		checker = Checker.ULTIMATE;
//		checker = Checker.IMPULSE;
		initialize(root);
		
		final boolean loop_forever = true; // for DEBUG
		final int iterationsLimit = 0; // for DEBUG
		
		ImpRootNode originalGraphCopy = copyGraph(m_graphRoot);
		
		m_graphWriter.writeGraphAsImage(originalGraphCopy, 
				String.format("graph_%s_original", m_graphWriter._graphCounter));


		int noOfProcedures = m_graphRoot.getOutgoingNodes().size();
//		noOfProcedures = 1;//TODO add SV-comp mode where only main is checked
		
		Result overallResult = Result.UNKNOWN;
		boolean allSafe = true;
		NestedRun<CodeBlock, AnnotatedProgramPoint> realErrorRun = null;
		RcfgProgramExecution realErrorProgramExecution = null;
		List<CodeBlock> realErrorFailurePath = null;
		
		for (int procID = 0; procID < noOfProcedures; ++procID) {
			AnnotatedProgramPoint procRoot = m_graphRoot.getOutgoingNodes().get(procID);
			s_Logger.debug("Exploring : " + procRoot);
			AnnotatedProgramPoint procedureRoot = procRoot;
			
			//FIXME
//			IEmptinessCheck emptinessCheck = new BFSEmptinessCheck();
			IEmptinessCheck emptinessCheck = new NWAEmptinessCheck();
			
			int iterationsCount = 0; // for DEBUG
			if (DEBUG)
				codeChecker.debug();
			while (loop_forever | iterationsCount++ < iterationsLimit) {
				s_Logger.debug(String.format("Iterations = %d\n", iterationsCount));
				NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun = 
						emptinessCheck.checkForEmptiness(procedureRoot);
				
				if (errorRun == null) {
					m_graphWriter.writeGraphAsImage(procedureRoot, 
						String.format("graph_%s_%s_noEP", m_graphWriter._graphCounter, procedureRoot.toString().substring(0, 5)));
					// if an error trace doesn't exist, return safe
					s_Logger.info("This Program is SAFE, Check terminated with " + iterationsCount + " iterations.");
					break;
				} else {
					s_Logger.info("Error Path is FOUND.");
					m_graphWriter.writeGraphAsImage(procedureRoot, 
						String.format("graph_%s_%s_foundEP", m_graphWriter._graphCounter, procedureRoot.toString().substring(0, 5)), 
						errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[]{}));
					
					TraceChecker traceChecker = new TraceChecker(
							m_truePredicate, // checks whether the trace is feasible, i.e. the formula is satisfiable
							m_falsePredicate,  //return LBool.UNSAT if trace is infeasible
							errorRun.getWord(),
							m_smtManager, 
							m_originalRoot.getRootAnnot().getModGlobVarManager(), 
							dumpInitialize());
					LBool isSafe = traceChecker.isCorrect();
					if(isSafe == LBool.UNSAT) { //trace is infeasible
						PredicateUnifier pu = new PredicateUnifier(m_smtManager, m_truePredicate, m_falsePredicate);
						traceChecker.computeInterpolants(new TraceChecker.AllIntegers(), pu);
						IPredicate[] interpolants = traceChecker.getInterpolants();
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
				assert originalGraphCopy.getOutgoingNodes().size() == noOfProcedures;
			}
			m_graphRoot = copyGraph(originalGraphCopy);
			codeChecker.m_graphRoot = m_graphRoot;
			assert m_graphRoot.getOutgoingNodes().size() == noOfProcedures;
			
			if (!allSafe)
				break;
		}

		if(DEBUG)
			codeChecker.debug();
		
		if (allSafe)
			overallResult = Result.CORRECT;
		else
			overallResult = Result.INCORRECT;
		
		
		s_Logger.info("-----------------");
		s_Logger.info(overallResult);
		s_Logger.info("-----------------");

		s_Logger.info("PC#: " + m_smtManager.getInterpolQueries());
		s_Logger.info("TIME#: " + m_smtManager.getInterpolQuriesTime());
//		s_Logger.info("ManipulationTIME#: " + m_smtManager.getTraceCheckTime());
		s_Logger.info("EC#: " + m_smtManager.getNontrivialSatQueries());
		s_Logger.info("TIME#: " + m_smtManager.getSatCheckTime());
//		s_Logger.info("ManipulationTIME#: "	+ m_smtManager.getCodeBlockCheckTime());

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
//			CounterExampleResult<CodeBlock> result = new CounterExampleResult<CodeBlock>(
//					realErrorRun.getWord().getSymbol(realErrorRun.getWord().length() - 1),
//					Activator.s_PLUGIN_NAME,
//					UltimateServices.getInstance().getTranslatorSequence(),
//					null, null);
			
			reportCounterexampleResult(realErrorRun.getWord().getSymbol(realErrorRun.getWord().length() - 1),
					AbstractCegarLoop.trace2path(realErrorFailurePath) , realErrorProgramExecution);
		
//			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, result);
		} else {
			UnprovableResult<CodeBlock> result = new UnprovableResult<CodeBlock>(null,
					Activator.s_PLUGIN_NAME,
					UltimateServices.getInstance().getTranslatorSequence(),
					null);
			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, result);
		}
		
		return false;
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