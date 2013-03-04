package de.uni_freiburg.informatik.ultimate.plugins.generator.reimpact;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.security.acl.LastOwnerException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.structure.IMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace.ErrorTrace;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace.IErrorTrace;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.AllIntegers;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

import org.apache.log4j.Logger;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class ReImpactObserver implements IUnmanagedObserver {
	public enum Result { CORRECT, TIMEOUT , MAXEDITERATIONS , UNKNOWN , INCORRECT }

	private static final int c_badNestingRelationInit = -7;

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private SmtManager m_smtManager;
	private int m_currentPreOrderIndex = 0;
	private TreeSet<UnwindingNode> m_openNodes;
	private ArrayList<UnwindingNode> m_allNodes;
	private TAPreferences m_taPrefs;
	
	RootNode m_graphRoot;
	
	private Result m_currentResult = Result.CORRECT;
	private IErrorTrace m_errorTrace = null;
	private NestedWord<CodeBlock> m_errorNW = null;
	private UnwindingNode m_currentUnwProcRoot;
	private boolean m_backToUnwind;
	private RootAnnot m_rootAnnot;
	
	private IPredicate m_truePredicate;
	private IPredicate m_falsePredicate;
	
	RIGraphWriter m_gw;
	int m_gwCounter = 0;
	
	//TODO revise forced covering before switching this on --> is matchLocation or equivalent used like in p_close?? 
	private boolean m_doForcedCovering = false;
	
	private HashMap<ProgramPoint, ArrayDeque<UnwindingNode>> m_locationToUnwindingNodes =
			new HashMap<ProgramPoint, ArrayDeque<UnwindingNode>>();
	private int m_fewRecent = 5;
	private UnwindingNode m_dummyUnwindingNode;
	private CodeBlock m_dummyCodeBlock;
	
	int m_pathChecks = 0;
	
	
	
	
	@Override
	public boolean process(IElement root) {
		assert c_badNestingRelationInit != NestedWord.INTERNAL_POSITION &&
				c_badNestingRelationInit != NestedWord.MINUS_INFINITY &&
				c_badNestingRelationInit != NestedWord.PLUS_INFINITY;
		
		m_graphRoot = (RootNode) root;
		m_rootAnnot = m_graphRoot.getRootAnnot();
		m_taPrefs = m_rootAnnot.getTaPrefs();
		m_smtManager = new SmtManager(m_rootAnnot.getBoogie2Smt(), 
				Solver.SMTInterpol, m_rootAnnot.getGlobalVars(), false, "");
		
		m_truePredicate = m_smtManager.newTruePredicate();
		m_falsePredicate = m_smtManager.newFalsePredicate();

//		m_gw = new RIGraphWriter("",//"C:/data/dumps",//"/home/alexander/reImpactGraphs",
		m_gw = new RIGraphWriter("C:/data/dumps",//"/home/alexander/reImpactGraphs",
				true, true, true, true, m_smtManager.getScript());
		
		for (IMultigraphEdge edge : m_graphRoot.getOutgoingEdges()) {
			ProgramPoint procRoot = (ProgramPoint) edge.getTarget();
			processProcedure(procRoot);
		}

		s_Logger.info("--------------");
		s_Logger.info(m_currentResult);
		s_Logger.info("--------------");
		
		s_Logger.info("PC#: " + m_smtManager.getInterpolQueries());
		s_Logger.info("TIME#: " + m_smtManager.getInterpolQuriesTime());
		s_Logger.info("ManipulationTIME#: " + m_smtManager.getTraceCheckTime());
		s_Logger.info("EC#: " + m_smtManager.getNontrivialSatQueries());
		s_Logger.info("TIME#: " + m_smtManager.getSatQuriesTime());
		s_Logger.info("ManipulationTIME#: "	+ m_smtManager.getCodeBlockCheckTime());
		
		if (m_currentResult == Result.CORRECT) {
			PositiveResult<CodeBlock> result = new PositiveResult<CodeBlock>(null,
					Activator.s_PLUGIN_NAME,
					UltimateServices.getInstance().getTranslatorSequence(),
					this.m_graphRoot.getPayload().getLocation());
			result.setShortDescription("Program is safe!");
			reportResult(result);
		} else if (m_currentResult == Result.INCORRECT) {
			this.reportResult(new CounterExampleResult<CodeBlock>(null,
					Activator.s_PLUGIN_NAME,
					UltimateServices.getInstance().getTranslatorSequence(),
					null, null));//m_errorTrace.getCounterExampleResult());
		} else {
			this.reportResult(new UnprovableResult<CodeBlock>(null,
					Activator.s_PLUGIN_NAME,
					UltimateServices.getInstance().getTranslatorSequence(),
					null));
		}
			
		return false;
	}

	/**
	 * process a single procedure (possibly with recursive calls to other procedures
	 */
	private void processProcedure(ProgramPoint procRoot) {
		m_currentPreOrderIndex = 0;
		m_openNodes = new TreeSet<UnwindingNode>(new UNWComparator());
		m_allNodes = new ArrayList<UnwindingNode>(); //(in preorder..) 
		
		m_currentUnwProcRoot = new UnwindingNode(
				m_truePredicate, procRoot, true);
		m_openNodes.add(m_currentUnwProcRoot);
		m_allNodes.add(m_currentUnwProcRoot);
		
		m_dummyUnwindingNode = new UnwindingNode(m_truePredicate, 
				m_currentUnwProcRoot.getProgramPoint(), null, //TODO: harter hack..
				-5); 
		m_dummyCodeBlock = new StatementSequence(
				null, 
				null, 
				new AssumeStatement(null, new BooleanLiteral(null, true)));
		//TODO: Could be replaced by connectSource, but this also 
		m_dummyCodeBlock.connectSource(null);
		m_dummyCodeBlock.setSource(m_currentUnwProcRoot.getProgramPoint());//TODO: harter hack..
		m_dummyCodeBlock.setTransitionFormula(
				new TransFormula(
						m_truePredicate.getFormula(), 
						new HashMap<BoogieVar, TermVariable>(),
						new HashMap<BoogieVar, TermVariable>(), 
						new HashSet<TermVariable>(0), 
						new HashSet<TermVariable>(0),
						TransFormula.Infeasibility.UNPROVEABLE,
						m_truePredicate.getFormula()));
		
		p_unwind();
	}
	
	private void p_unwind() {
		m_gw.writeGraphAsImage(m_currentUnwProcRoot, 
				"grph_" + (++m_gwCounter) + "_processProc" , m_openNodes);
		
		while (!m_openNodes.isEmpty()) {
			UnwindingNode currentNode = m_openNodes.pollFirst();
			
			for (int i = 0; i < currentNode.getPreOrderIndex(); i++) 
				p_close(m_allNodes.get(i));

			p_dfs(currentNode);
			m_backToUnwind = false;
		}
	}
	
	private void p_dfs(UnwindingNode node) {
//		m_gw.writeGraphAsImage(m_currentUnwProcRoot, "grph_" + (++m_gwCounter) + "_dfs" , m_openNodes);
		
		if (m_currentResult == Result.INCORRECT || m_backToUnwind)
			return;
		
		p_close(node);
		if (!node.isCovered()) {
			if (node.isErrorLocation()) {
				p_refine(node);
				for (int i = 0; i <= node.getPreOrderIndex(); i++)
					p_close(m_allNodes.get(i));
			}
			p_expand(node);
			for (RIAnnotatedProgramPoint app : node.getOutgoingNodes())
				p_dfs((UnwindingNode) app);
				
		}
	}

	private void p_expand(UnwindingNode node) {
		if (node.isLeaf()) {
			if (m_doForcedCovering &&
					m_locationToUnwindingNodes.get(node.getProgramPoint()) != null)
				for (UnwindingNode un : m_locationToUnwindingNodes.get(node.getProgramPoint()))
					if (node.getPreOrderIndex() > un.getPreOrderIndex() && 
							p_forceCover(node, un))
						return;
			
			assert !node.isCovered();
			unwindNode(node);
			m_gw.writeGraphAsImage(m_currentUnwProcRoot, "grph_" + (++m_gwCounter) + "_expand" , m_openNodes);
		}
	}

	private void p_refine(UnwindingNode node) {
		assert node.isErrorLocation() &&
			!node.getPredicate().getFormula().equals(m_smtManager.getScript().term("false"));
		
		//Pair<UnwindingNode[], NestedWord<CodeBlock>> errorNWP = getErrorPathAsNestedWord(node);
		Pair<UnwindingNode[], CodeBlock[]> errorPath = getPath(node, null);
		
		int[] nestingRelation = computeNestingRelation(errorPath.getSecond());
		
//		if (nestingRelation[0] == c_badNestingRelationInit) {
//			cutBadReturnEdgeAndBelow(errorPath, nestingRelation[1]);
//			setPreCallNodeImportantFlags(errorPath.getFirst(), nestingRelation[2], nestingRelation[1]);
//			m_backToUnwind = true; //all nodes below have been closed, update openNodes we are working on
//			return;
//		} else 
//		if (getFirstPendingReturnIndex(nestingRelation) != -1) {
//			setPreCallNodeImportantFlags(errorPath.getFirst(), 0, getFirstPendingReturnIndex(nestingRelation));
//			return;
//		}
		
		NestedWord<CodeBlock> errorPathAsNestedWord = 
				new NestedWord<CodeBlock>(errorPath.getSecond(), nestingRelation); 
		
		Pair<UnwindingNode[], NestedWord<CodeBlock>> errorNWP =
				new Pair<UnwindingNode[], NestedWord<CodeBlock>>(
						errorPath.getFirst(), errorPathAsNestedWord);

		TraceChecker traceChecker = new TraceChecker(m_smtManager, 
				m_rootAnnot.getModifiedVars(),
				m_rootAnnot.getEntryNodes(),				
				dumpInitialize());
		LBool isSafe = traceChecker.checkTrace(m_truePredicate, 
				m_falsePredicate, 
				errorNWP.getSecond());
		m_pathChecks++;
		
		if (isSafe == LBool.UNSAT) {
			IPredicate[] interpolants = traceChecker.getInterpolants(new TraceChecker.AllIntegers());
			refineTrace(errorNWP, interpolants);
			setPreCallNodeImportantFlags(errorNWP.getFirst(), 0, getFirstPendingReturnIndex(nestingRelation));
		} else {
			traceChecker.forgetTrace();
			if (isSafe == LBool.SAT)
				m_currentResult = Result.INCORRECT;
			else if (isSafe == LBool.UNKNOWN)
				m_currentResult = Result.UNKNOWN;
			NestedWord<CodeBlock> errorNW = errorNWP.getSecond();
			m_openNodes.clear();
			m_backToUnwind = true;

			//error reporting stuff			
//			makeErrorTraceFromNW(errorNW); 
		}
		m_gw.writeGraphAsImage(m_currentUnwProcRoot, "grph_" + (++m_gwCounter) + "_refine" , m_openNodes);
	}

//	private void cutBadReturnEdgeAndBelow(
//			Pair<UnwindingNode[], CodeBlock[]> errorPath, int returnEdgeIndex) {
//		UnwindingNode returnEdgeSource = errorPath.getFirst()[returnEdgeIndex];
//		assert returnEdgeSource.getOutgoingEdgeLabel(errorPath.getFirst()[returnEdgeIndex + 1])
//		  instanceof Return;
//		returnEdgeSource.removeOutgoingNode(errorPath.getFirst()[returnEdgeIndex + 1]);
////		ArrayList<RIAnnotatedProgramPoint> list = new ArrayList<RIAnnotatedProgramPoint>();
////		list.add(errorPath.getFirst()[returnEdgeIndex + 1]);
////		coverRec(list);
//		//remove the whole tree below -- it should suffice to remove the nodes from the global lists
//		removeSubtreeFromLists(errorPath.getFirst()[returnEdgeIndex + 1]);
//	}
//
//	private void removeSubtreeFromLists(RIAnnotatedProgramPoint root) {
//		this.m_allNodes.set(((UnwindingNode) root).getPreOrderIndex(), null);
//		this.m_openNodes.remove(root);
//		for (RIAnnotatedProgramPoint app : root.getOutgoingNodes()) {
//			removeSubtreeFromLists(app);
//		}
//	}

	private int getFirstPendingReturnIndex(int[] nestingRelation) {
		for (int i = 0; i < nestingRelation.length; i++)
			if (nestingRelation[i] == NestedWord.MINUS_INFINITY)
				return i;
		return -1;
	}

	private void makeErrorTraceFromNW(NestedWord<CodeBlock> errorNW) {
		ArrayList<IElement> errorPathAL = new ArrayList<IElement>();
		Term[] errorPathFormulas = new Term[errorNW.length()];
		for (int i = 0; i < errorNW.length(); i++) { 
			errorPathAL.add(errorNW.getSymbolAt(i));
			errorPathFormulas[i] = errorNW.getSymbolAt(i).getTransitionFormula().getFormula();
		}
		m_errorTrace = new ErrorTrace(m_smtManager.getScript(), errorPathAL, errorPathFormulas);
	}

	private void refineTrace(
			Pair<UnwindingNode[], NestedWord<CodeBlock>> errorNW,
			IPredicate[] interpolants) {
		for (int i = 0; i < interpolants.length; i++) {
			UnwindingNode pathNode = errorNW.getFirst()[i+1];
			
			if (m_smtManager.isCovered(pathNode.getPredicate(), interpolants[i])
					!= LBool.UNSAT) {
				removeAllCoverings(pathNode);
				
				TermVarsProc tvp = m_smtManager.and(pathNode.getPredicate(), interpolants[i]);
				pathNode.setPredicate(m_smtManager.newPredicate(tvp.getFormula(), 
						tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula()));
			}
		}
	}

	/**
	 * All covering edges leading to the given node are removed.
	 * Call this when the annotation of a node has been strengthened (by formula or flag).
	 * @param pathNode
	 */
	private void removeAllCoverings(UnwindingNode pathNode) {
		uncoverRec(new ArrayList<RIAnnotatedProgramPoint>(pathNode.m_coveredNodes));
		pathNode.m_coveredNodes.clear();
		if (pathNode.isLeaf())
			m_openNodes.add(pathNode);
		else
			uncoverRec(pathNode.getOutgoingNodes());
	}

	private void setPreCallNodeImportantFlags(
			UnwindingNode[] errorPath, int startIndex, int endIndex) {
		for (int i = startIndex; i < endIndex; i++) {//TODO border cases??
			errorPath[i].setPreCallNodeImportant(true);
			removeAllCoverings(errorPath[i]);
		}
	}

	private void p_close(UnwindingNode node) {
//		m_gw.writeGraphAsImage(m_currentUnwProcRoot, "grph_" + (++m_gwCounter) + "_close" , m_openNodes);
		for (int i = 0; i < node.getPreOrderIndex(); i++) 
			if (m_allNodes.get(i) != null &&
					!node.equals(m_allNodes.get(i)) && 
					node.matchLocationForCovering(m_allNodes.get(i)) &&
					!m_allNodes.get(i).m_isCovered)
					p_cover(node, m_allNodes.get(i));
	}

	private void p_cover(UnwindingNode coveringSource,
			UnwindingNode coveringTarget) {
//		m_gw.writeGraphAsImage(m_currentUnwProcRoot, "grph_" + (++m_gwCounter) + "_coverA" , m_openNodes);
		if (!coveringSource.isCovered() &&
				coveringSource.getPreOrderIndex() > coveringTarget.getPreOrderIndex()) {
							
			if (m_smtManager.isCovered(
					coveringSource.getPredicate(),
					coveringTarget.getPredicate()) 
					== LBool.UNSAT
					//the following is already done in matchLocation for covering by p_close
					//&& (!coveringTarget.isPreCallNodeImportant || preCallNodesMatch(coveringSource, coveringTarget))
					) {
				coveringSource.m_isCovered = true;
				coveringSource.m_coveringNode = coveringTarget;
				coveringTarget.m_coveredNodes.add(coveringSource);
				
				m_openNodes.remove(coveringSource);
				coverRec(coveringSource.getOutgoingNodes());

				m_gw.writeGraphAsImage(m_currentUnwProcRoot, "grph_" + (++m_gwCounter) + "_coverB" , m_openNodes);
			}
		}
	}
	
    private boolean preCallNodesMatch(UnwindingNode coveringSource,
			UnwindingNode coveringTarget) {
    	
    	UnwindingNode pc1 = findLastPreCallNode(coveringSource);
     	UnwindingNode pc2 = findLastPreCallNode(coveringTarget);   	
     	if (pc1 == null || pc2 == null)
     		if (pc1 == null && pc2 == null)
     			return true;
     		else
     			return false;
     	else 
     		return pc1.equals(pc2);
	}

	/**
     * follows edges upwards to the root, returns the node  before the first call it sees
     * could be replaced by a field in UnwindingNode -- what is faster??
     */
	private UnwindingNode findLastPreCallNode(UnwindingNode node) {
		UnwindingNode currentNode = node;
		if(currentNode.getIncomingNodes().isEmpty())
			return null;
		Object currentEdge = 
				currentNode.getIncomingEdgeLabel(
						(RIAnnotatedProgramPoint) currentNode.getIncomingNodes().get(0));
		while (!(currentEdge instanceof Call)) {
			currentNode = (UnwindingNode) currentNode.getIncomingNodes().get(0);
			if(currentNode.getIncomingNodes().isEmpty())
				return null;
			currentEdge = 
					currentNode.getIncomingEdgeLabel(
							(RIAnnotatedProgramPoint) currentNode.getIncomingNodes().get(0));	
		}
		return (UnwindingNode) currentNode.getIncomingNodes().get(0);
	}

	/**
	 * for each given element recursively (going down) remove all covering edges connected to it
	 * and mark it as covered (by a node above of it by convention..)
	 */
	private void coverRec(List<RIAnnotatedProgramPoint> outgoingNodes) {
		if(outgoingNodes == null) return;
		for(RIAnnotatedProgramPoint iNode : outgoingNodes) {
			UnwindingNode unwNode = (UnwindingNode) iNode;
			
			unwNode.m_isCovered = true;
			m_openNodes.remove(unwNode);
			
			if(unwNode.m_coveringNode != null) 
				unwNode.m_coveringNode.m_coveredNodes.remove(unwNode);
			
			for(UnwindingNode un : unwNode.m_coveredNodes) {
				un.m_coveringNode = null;
				un.m_isCovered = false;				
				assert un.m_coveredNodes.size() == 0;
				
				if(un.isLeaf()) 
					m_openNodes.add(un);
				
				uncoverRec(un.getOutgoingNodes()); 
			}
			unwNode.m_coveredNodes.clear();
			unwNode.m_coveringNode = null;
			
			coverRec(unwNode.getOutgoingNodes());
		}
	}
	
	/**
	 * for each given element recursively (going down) set isCovered false and 
	 * clear the coveringNodes List 
	 */
	private void uncoverRec(List<RIAnnotatedProgramPoint> arrayList) {
		if(arrayList == null) return;
		for(RIAnnotatedProgramPoint iNode : arrayList) {
			UnwindingNode unwNode = (UnwindingNode) iNode;
			unwNode.m_isCovered = false;
			if(unwNode.isLeaf()) {
				m_openNodes.add(unwNode);	
			}
			if(unwNode.m_coveringNode != null) {
				unwNode.m_coveringNode = null;
			}
			uncoverRec((List<RIAnnotatedProgramPoint>) unwNode.getOutgoingNodes());
		}
	}

	private void unwindNode(UnwindingNode node) {
		m_openNodes.remove(node);
		node.setIsLeaf(false);
		for (IMultigraphEdge outEdge : node.getProgramPoint().getOutgoingEdges()) {
			ProgramPoint target = (ProgramPoint) outEdge.getTarget();
			
			if (outEdge instanceof Summary)
				continue;
			
			//do not unwind return edges that do not fit the last call
			//set flags in this case
			if (outEdge instanceof Return) {
				Pair<UnwindingNode[], CodeBlock[]> path = getPath(node, null);
				if(node.getPreCallNode() == null) {//do not unwind return edges when we have not seen a call
					setPreCallNodeImportantFlags(path.getFirst(), 0, path.getFirst().length);
					continue;
				} else if (!((Return) outEdge).getCallerNode().equals(node.getPreCallNode().getProgramPoint())) {
					int matchingPreCallIndex = 
							getIndexOfPreCallOnPath(path.getFirst(), node.getPreCallNode());
					setPreCallNodeImportantFlags(path.getFirst(), matchingPreCallIndex + 1,
							path.getFirst().length);
					continue;
				}
			}
					
			Stack<UnwindingNode> preCallNodeStack = (Stack<UnwindingNode>) node.m_preCallNodeStack.clone();
			if (outEdge instanceof Call) 
				preCallNodeStack.push(node);
			else if (outEdge instanceof Return && !preCallNodeStack.isEmpty()) 
				preCallNodeStack.pop();
			
			UnwindingNode newNode = null;
			
			if (target.isErrorLocation()) {
				newNode = new UnwindingNode(
						m_truePredicate, target, 
						preCallNodeStack,
						-m_currentPreOrderIndex);//was the "-" here a bug??
				//needed for termination: once we have seen 
				//a new error location we have to refine
				m_backToUnwind = true; 
			} else {
				newNode = new UnwindingNode(
						m_truePredicate, target, 
						preCallNodeStack,
						++m_currentPreOrderIndex);
				m_allNodes.add(newNode);
				
				ArrayDeque<UnwindingNode> list = 
						m_locationToUnwindingNodes.get(newNode.getProgramPoint());
				if (list == null)
					list = new ArrayDeque<UnwindingNode>();
				list.add(newNode);
				if (list.size() > m_fewRecent)
					list.pollFirst();
				m_locationToUnwindingNodes.put(newNode.getProgramPoint(), list);
			}
			
			node.addOutgoingNode(newNode, (CodeBlock) outEdge);
			//newNode.addIncomingNode(node, (CodeBlock) outEdge);//the add.. method treats both nodes now
			
			newNode.setIsLeaf(true);
			m_openNodes.add(newNode);
		}
	}
	
	private int getIndexOfPreCallOnPath(UnwindingNode[] path, UnwindingNode preCallUnwNode) {
		for (int i = 0; i < path.length; i++)
			if (path[i].equals(preCallUnwNode))
				return i;
		assert false;
		return -1;
	}

	private Call findLastCall(UnwindingNode node) {
		UnwindingNode currentNode = node;
		if(currentNode.getIncomingNodes().isEmpty())
			return null;
		Object currentEdge = 
				currentNode.getIncomingEdgeLabel(
						(RIAnnotatedProgramPoint) currentNode.getIncomingNodes().get(0));
		while (!(currentEdge instanceof Call)) {
			currentNode = (UnwindingNode) currentNode.getIncomingNodes().get(0);
			if(currentNode.getIncomingNodes().isEmpty())
				return null;
			currentEdge = 
					currentNode.getIncomingEdgeLabel(
							(RIAnnotatedProgramPoint) currentNode.getIncomingNodes().get(0));	
		}
		return (Call) currentEdge;
	}

	private boolean p_forceCover(UnwindingNode v, UnwindingNode w) {
		assert (v.getPreOrderIndex() > w.getPreOrderIndex());
		
		UnwindingNode x = getNearestCommonAncestorOf(v, w);
		
		Pair<UnwindingNode[], NestedWord<CodeBlock>> newPathNWP = 
				prolongNestedWordUnwNodePair(v, x);
		
		TraceChecker traceChecker = new TraceChecker(m_smtManager, 
				m_rootAnnot.getModifiedVars(),
				m_rootAnnot.getEntryNodes(),
				dumpInitialize());
		
		LBool isSafe = traceChecker.checkTrace(v.getPredicate(), w.getPredicate(), newPathNWP.getSecond());
		
		if (isSafe == LBool.UNSAT) {
			IPredicate[] interpolants = traceChecker.getInterpolants(new TraceChecker.AllIntegers());
			refineTrace(newPathNWP, interpolants);
			p_cover(v, w); //FIXME: cover does an implication check which is not necessary, here
			assert v.m_isCovered && v.m_coveringNode == w;
			return true;
		} else {
			traceChecker.forgetTrace();
			return false;
		}
	}

	private Pair<UnwindingNode[], NestedWord<CodeBlock>> prolongNestedWordUnwNodePair(
			UnwindingNode v, UnwindingNode x) {
		
		Pair<UnwindingNode[], NestedWord<CodeBlock>> pathNWP = getErrorPathAsNestedWord(v, x);
		
		UnwindingNode[] newFirst = new UnwindingNode[pathNWP.getFirst().length+2];
		for (int i = 0; i < newFirst.length; i++)
			if (i == 0 || i == newFirst.length - 1)
				newFirst[i] = m_dummyUnwindingNode;
			else
				newFirst[i] = pathNWP.getFirst()[i-1];
		
		NestedWord<CodeBlock> oldNW = pathNWP.getSecond();
		
		int[] newNestingRelation = new int[oldNW.length() + 2];
		for (int i = 0; i < newNestingRelation.length; i++)
			if (i == 0 || i == newNestingRelation.length -1)
				newNestingRelation[i] = -2;
			else
				if (oldNW.isInternalPosition(i-1))
					newNestingRelation[i] = -2;
				else if (oldNW.isCallPosition(i-1))
					newNestingRelation[i] = oldNW.getReturnPosition(i-1) + 1;
				else if (oldNW.isReturnPosition(i-1))
					newNestingRelation[i] = oldNW.getCallPosition(i-1) + 1;
		
		CodeBlock[] newCodeBlocks = new CodeBlock[oldNW.length() + 2];
		for (int i = 0; i < newCodeBlocks.length; i++)
			if (i == 0 || i == newCodeBlocks.length -1)
				newCodeBlocks[i] = m_dummyCodeBlock;
			else
				newCodeBlocks[i] = oldNW.getSymbolAt(i-1);
		
		NestedWord<CodeBlock> newNW = new NestedWord<CodeBlock>(newCodeBlocks, newNestingRelation);
		
		Pair<UnwindingNode[], NestedWord<CodeBlock>> newPathNWP= new Pair<UnwindingNode[], NestedWord<CodeBlock>>(newFirst, newNW);
		return newPathNWP;
	}
	
	/**
	 * computes the paths to the root of each v and w, and returns the last node
	 * where the nodes are equal on both paths
	 * @param v
	 * @param w
	 * @return
	 */
	private UnwindingNode getNearestCommonAncestorOf(UnwindingNode v,
			UnwindingNode w) {
		UnwindingNode[] pathV = getPath(v, null).getFirst();
		UnwindingNode[] pathW = getPath(w, null).getFirst();
		
		int i;
		for (i = 0; i < pathW.length && pathV[i].equals(pathW[i]); i++);
			
		return pathV[i-1];
	}

	
	
	private Pair<UnwindingNode[], CodeBlock[]> getPath(
			UnwindingNode errorLocation, UnwindingNode border) {
		ArrayList<UnwindingNode> nodes = new ArrayList<UnwindingNode>();
		ArrayList<CodeBlock> edges = new ArrayList<CodeBlock>();
		
		UnwindingNode currentNode = errorLocation;
		
		while (currentNode != border && !currentNode.m_isProcRoot) {
			assert(currentNode != null);
			nodes.add(currentNode);
			UnwindingNode incomingNode = (UnwindingNode) currentNode.getIncomingNodes().get(0);
			CodeBlock edge = currentNode.getIncomingEdgeLabel(
					incomingNode);
			currentNode = incomingNode;
			edges.add(edge);
		}
		nodes.add(currentNode); //add the procRoot, too
		
		Collections.reverse(nodes);
		Collections.reverse(edges);
		
		UnwindingNode[] nodeArray = new UnwindingNode[nodes.size()];
		CodeBlock[] edgeArray = new CodeBlock[edges.size()];
		nodes.toArray(nodeArray);
		edges.toArray(edgeArray);
		
		return new Pair<UnwindingNode[], CodeBlock[]>(nodeArray, edgeArray);
	}
	
	// --------------------------------------------------
	// -------------- from chainsawEngine -------------------
	// --------------------------------------------------
	
	public Pair<UnwindingNode[], NestedWord<CodeBlock>> getErrorPathAsNestedWord(
			UnwindingNode errorLocation) {
		return getErrorPathAsNestedWord(errorLocation, null);
	}
	
	public Pair<UnwindingNode[], NestedWord<CodeBlock>> getErrorPathAsNestedWord(
			UnwindingNode errorLocation, UnwindingNode border) {
		Pair<UnwindingNode[], CodeBlock[]> errorPath = getPath(errorLocation, border);
		
		int[] nestingRelation = computeNestingRelation(errorPath.getSecond());
		
		NestedWord<CodeBlock> errorPathAsNestedWord = 
				new NestedWord<CodeBlock>(errorPath.getSecond(), nestingRelation); 
		
		return new Pair<UnwindingNode[], NestedWord<CodeBlock>>(
				errorPath.getFirst(), errorPathAsNestedWord);
	}

	/**
	 * Compute the nesting relation for a given error path in the NestedWord format from Matthias.
	 * Also does a sanity check: If there is a Return following a Call that it does not fit to, a
	 * special array is returned. This Array is of the form {special constant, first non-matching-
	 * return-index, non-matching-call index}
	 */
	private static int[] computeNestingRelation(CodeBlock[] errorPath) {
		int [] nr = new int[errorPath.length];
		Stack<Call> callStack = new Stack<Call>();
		Stack<Integer> callStackIndizes = new Stack<Integer>();
		for (int i = 0; i < nr.length; i++) {
			if (errorPath[i] instanceof Call) {
				nr[i] = -2;
				callStack.push((Call) errorPath[i]);
				callStackIndizes.push(i);
			} else if (errorPath[i] instanceof Return) {
				if (callStackIndizes.isEmpty()) {
					nr[i] = NestedWord.MINUS_INFINITY;
					break;
				}
				Call matchingCall = callStack.pop();
				if (((Return) errorPath[i]).getCorrespondingCallAnnot().equals(matchingCall)) {
					nr[i] = callStackIndizes.pop();
					nr[nr[i]] = i;	
				} else {
					return new int[] {c_badNestingRelationInit , i, callStackIndizes.pop()};
				}
				
			} else {
				nr[i] = NestedWord.INTERNAL_POSITION;
			}
		}
		//calls that are still on the stack are pending
		for (Integer i : callStackIndizes)
			nr[i] = NestedWord.PLUS_INFINITY;
		return nr;
	}
	
	private PrintWriter dumpInitialize() {
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
	
	private void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
	}
	
	// --------------------------------------------------
	// -------------- interface stuff -------------------
	// --------------------------------------------------
	
	@Override
	public void finish() {
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public void init() {
		
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	
	/**
	 * the comparator for UnwindingNodes: It takes care that Error Locations are 
	 * always sorted in at the beginning and, at second priority, takes the order of the 
	 * expansion of the nodes into account - sort of preorder..
	 */
	class UNWComparator implements Comparator<UnwindingNode> {

		@Override
		public int compare(UnwindingNode o1, UnwindingNode o2) {
			if(o1.isErrorLocation()) 
				if(o2.isErrorLocation()) 
					if(o1.equals(o2))
						return 0;
					else
						return -1;
				else 
					return -1;				
			else if (o2.isErrorLocation())
				return 1;
			else 
				return o1.getPreOrderIndex() - o2.getPreOrderIndex();	
		}

	}
}
