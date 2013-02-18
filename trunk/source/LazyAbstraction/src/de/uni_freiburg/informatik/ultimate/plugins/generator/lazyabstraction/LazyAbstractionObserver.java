package de.uni_freiburg.informatik.ultimate.plugins.generator.lazyabstraction;

import org.apache.log4j.Logger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.TreeSet;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.CFGRootAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SCNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace.ErrorTrace;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.FormulaArrayBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.SMTInterface;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.Const2VariableTermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.StripAnnotationsTermTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.lazyabstraction.preferences.PreferenceConstants;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;

/**
 * Implementation of the algorithm from Ken McMillan's paper "Lazy Abstraction with Interpolants".
 * The core methods are named according to the methods of the paper's pseudo code.
 * A control flow graph from ErrorLocationGenerator is taken as input and a safety check of 
 * the program's assertions is executed.
 */
public class LazyAbstractionObserver implements IUnmanagedObserver {

	private static Logger s_logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private UnwindingNode m_graphroot;
	private HashMap<Term, BoogieVar>		m_ConstantsToBoogieVar	= new HashMap<Term, BoogieVar>();
	private FormulaArrayBuilder m_formulaArrayBuilder = null;
	private Script m_script;
	private TreeSet<UnwindingNode> m_openNodes;
	TreeSet<UnwindingNode> coveredToRemove;
	CFGRootAnnotations m_cfgRootAnnotations;
	HashMap<String, Procedure> m_procDeclarationsByName;
	
	private SMTInterface m_SMTInterface;
	
	private boolean m_programIncorrect = false;
	StringBuilder m_errorPath;
	
	private boolean m_returnToUnwind;

	HashMap<String,ArrayDeque<TermVariable>> m_availableTermVariables 
		= new HashMap<String,ArrayDeque<TermVariable>>();
	HashMap<String,ArrayDeque<TermVariable>> m_usedTermVariables 
		= new HashMap<String,ArrayDeque<TermVariable>>();
	
	boolean m_doMemoization;
	
	int noUnwind = 0;
	int noCover = 0;
	int noExpand = 0;
	int noClose = 0;
	int noDfs = 0;
	int noRefine = 0;
	int noNodes = 0;
	int noImplicationChecks = 0;
	int noErrorPathChecks = 0;
	long timeErrorPathChecks = 0;
	
	GraphWriter gw;
	private StripAnnotationsTermTransformer m_stripAnnotationsTT = new StripAnnotationsTermTransformer();

	int countExpand = 0;
	private ArrayList<IElement> m_errorTrace = null;
	private Term[] m_errorTraceFormulas = null;
	
	@Override
	public boolean process(IElement node) {
		
		m_doMemoization = Activator.getDefault().getPreferenceStore()
		  .getBoolean(PreferenceConstants.P_MEMOIZE);

		CFGExplicitNode root	= (CFGExplicitNode) node;
		m_script = ((CFGRootAnnotations)root
				.getPayload().getAnnotations().get("CFGBuilder")).getScript();
		m_SMTInterface = new SMTInterface(m_script);
		m_formulaArrayBuilder = new FormulaArrayBuilder(m_script);
		
		gw = new GraphWriter(
				Activator.getDefault()
				  .getPreferenceStore().getString(PreferenceConstants.P_IMAGE_PATH),
				Activator.getDefault().getPreferenceStore()
				  .getBoolean(PreferenceConstants.P_ANNOTATE_EDGES),
				Activator.getDefault().getPreferenceStore()
				  .getBoolean(PreferenceConstants.P_ANNOTATE_NODES),
				Activator.getDefault().getPreferenceStore()
				  .getBoolean(PreferenceConstants.P_SHOW_UNREACHABLE),
				false, m_script);

		gw.writeGraphAsImage(root, "cfg");
		
		m_graphroot = new UnwindingRoot(root);
		
		for (INode n : root.getOutgoingNodes()) {
			gw.writeGraphAsImage(m_graphroot, "graph_a_init" + ((CFGExplicitNode)n).toString());
			
			processProcedure((CFGExplicitNode) n);
		}
		
		if(m_programIncorrect) {
			ErrorTrace errorTrace = new ErrorTrace(m_script, m_errorTrace, m_errorTraceFormulas);
			this.reportResult(errorTrace.getCounterExampleResult());

			s_logger.info(" ------------- P R O G R A M   U N S A F E ------------------- ");
			s_logger.info(m_errorPath);
		} else {
			PositiveResult result = new PositiveResult(null,
					Activator.s_PLUGIN_NAME,
					UltimateServices.getInstance().getTranslatorSequence(),
					m_graphroot.getPayload().getLocation());
			result.setShortDescription("Program is safe!");
			reportResult(result);
			s_logger.info(" ------------- P R O G R A M   S A F E ------------------- ");
		}
		logStats();
		gw.writeGraphAsImage(m_graphroot, "graph_z_final", m_openNodes);
		
		return false;
	}

	/**
	 * performs a safety check for each procedure
	 */
	public void processProcedure(CFGExplicitNode cfgProcNode) {
		
		if(cfgProcNode.getOutgoingEdges().size() == 0) {
			checkInCaseOfNoOutgoingEdges(cfgProcNode);
			return;
		}

		m_openNodes = new TreeSet<UnwindingNode>(new UNWComparator());
		
		UnwindingProcRoot procRoot = new UnwindingProcRoot(cfgProcNode);

		CFGEdge edge = new CFGEdge(m_script, m_script.term("true"), m_graphroot, procRoot);
		procRoot.addIncomingEdge(edge);
		m_graphroot.addOutgoingEdge(edge);
		
		if(cfgProcNode.getOutgoingEdges().isEmpty()) {
			m_openNodes.add(procRoot); 
		} else {
			procRoot.unwindNode(m_openNodes);
		}
		
		paper_UNWIND();
	}

	private void checkInCaseOfNoOutgoingEdges(CFGExplicitNode cfgProcNode) {
		if (!cfgProcNode.getPayload().getName().contains("ERROR")) {
			m_programIncorrect = false;
		} else {
			m_errorTrace = new ArrayList<IElement>();
			m_errorTrace.add(m_graphroot);

			CFGEdge edge = new CFGEdge(m_script, m_script.term("true"), 
					m_graphroot, cfgProcNode);
			cfgProcNode.addIncomingEdge(edge);
			m_graphroot.addOutgoingEdge(edge);
			m_errorTrace.add(edge);
			m_errorTrace.add(cfgProcNode);
			
			//HACK: we know unsafe from ELG, but the ELG has popped...
			//we also need getFormulas for the SCAnnotations
			Term[] itps = m_SMTInterface.computeInterpolants( 
					m_formulaArrayBuilder.getFormulas(m_errorTrace));
			assert itps == null;
			
			m_errorTraceFormulas = new Term[m_errorTrace.size()-2];
			IElement el = m_errorTrace.get(2);
			m_errorTraceFormulas[0] = ((CFGExplicitNode)el).getAssertion();
			
			m_programIncorrect = true;
		}
	}


	@SuppressWarnings("unchecked")
	private void paper_UNWIND() {
		noUnwind++;
		
		while (!m_openNodes.isEmpty()) {
				s_logger.debug("UNWIND: loop started again with " + m_openNodes);

			if (m_programIncorrect) return;
			m_returnToUnwind = false;
			
			TreeSet<UnwindingNode> openNodes_0 = 
				(TreeSet<UnwindingNode>) m_openNodes.clone();
			
			for (UnwindingNode openNode : openNodes_0) {
				if(openNode.getIncomingEdges().size() > 0)
					closeRec((UnwindingNode)(openNode.getIncomingEdges().get(0).getSource()));

				assert(openNode.isLeaf());
				paper_DFS(openNode);
			}
		}
	}

	private void logStats() {
		long edgeChecksTime = ((CFGEdge) m_graphroot.getOutgoingEdges().get(0))
				.getTotalTime();
		String s = "stats: \n" 
			+ "dfs: " + noDfs + "\n"
			+ "close: " + noClose + "\n"
			+ "expand: " + noExpand + "\n"
			+ "refine: " + noRefine + "\n"
			+ "cover: " + noCover + "\n"
			+ "BMdata:(Lazy Abstraction)SPLIT: unwinding nodes: " 
			+ noNodes + "\n"
			+ "BMdata:(Lazy Abstraction) error path checks: (5)PC#: " 
			+ noErrorPathChecks + "\n"
			+ "BMdata:(Lazy Abstraction) error path checks: (6)TIME#: " 
			+ timeErrorPathChecks + "\n"
			+ "BMdata:(Edge Checks) implication checks: (7)EC#: "
			+ noImplicationChecks + "\n"
			+ "BMdata:(Edge Checks) implication checks: (8)TIME#: " 
			+ edgeChecksTime;
		s_logger.info(s);
	}
	
	/**
	 * calls CLOSE recursively on all nodes going upwards to the procroot
	 */
	private void closeRec(UnwindingNode unwNode) {
		if (!(unwNode instanceof UnwindingProcRoot)) {
			paper_CLOSE(unwNode);
			UnwindingNode parent = 
					(UnwindingNode)(unwNode.getIncomingEdges().get(0).getSource());
			if (!(parent instanceof UnwindingProcRoot)) {
				closeRec(parent);
			}
		}
	}
	
	private void paper_DFS(UnwindingNode v) {
		noDfs++;
		if (m_programIncorrect) return;
		
		s_logger.debug("DFS has been called");
		logStats();
		
		if (m_returnToUnwind) 
			return; 
		
		paper_CLOSE(v);
		if (v.isErrorLocation()) {
			paper_REFINE(v);
			if (m_programIncorrect) return;
			closeRec(v);
		}
		paper_EXPAND(v);
		
		for (int i = 0; i < v.getOutgoingEdges().size(); i++) {
			CFGEdge unwEdge = (CFGEdge) v.getOutgoingEdges().get(i);
			paper_DFS((UnwindingNode) unwEdge.getTarget());
		}
	}
	
	private void paper_EXPAND(UnwindingNode unwNode) {
		noExpand++;
		
//		gw.writeGraphAsImage(unwNode, "graph_b_procProced" + countExpand++, m_openNodes);
		
		s_logger.debug("EXPAND: open Nodes: " + m_openNodes);

		if (m_openNodes.contains(unwNode)) { //(!unwNode.isCovered() && unwNode.isLeaf()) {
			assert !unwNode.isCovered() && unwNode.isLeaf();
			unwNode.set_isLeaf(false);
			m_openNodes.remove(unwNode);
			unwNode.unwindNode(m_openNodes);
		}
		
		s_logger.debug("open Nodes after: " + m_openNodes);
	}

	private void paper_REFINE(UnwindingNode v) {
		assert v.isErrorLocation();
		s_logger.debug("REFINE has been called");
		
		noRefine++;

		if (!v.getSMTAnnotations().getAssertion().equals(m_script.term("false"))) {
			ArrayList<IElement> path = getPath(v, new ArrayList<IElement>());
			
			Term[] formulas = m_formulaArrayBuilder.getFormulas(path);
			
			StringBuilder sb = new StringBuilder();
			for(int i = 0; i < formulas.length; i++) {
				sb.append("\n");
				sb.append(m_stripAnnotationsTT.transform(formulas[i]));
			}
			s_logger.debug("path: " + sb.toString());

			long startTime = System.currentTimeMillis();
			Term[] interpolants = m_SMTInterface.computeInterpolants(formulas);
			timeErrorPathChecks += (System.currentTimeMillis() - startTime);
			noErrorPathChecks++;
			
			if(interpolants != null) {
				
				s_logger.debug("REFINE: generated sequence of interpolants");
				
				for(int i = 0; i < interpolants.length; i++) {
					UnwindingNode nodeOnPath = (UnwindingNode) path.get(i*2+4); 
					
					SMTNodeAnnotations smtAnnotations = 
						(SMTNodeAnnotations) nodeOnPath.getPayload().getAnnotations().get("SMT");
					
					SCNodeAnnotations scAnnotations = (SCNodeAnnotations)nodeOnPath.
							getPayload().getAnnotations().get("SC");
					if (scAnnotations == null) {
						scAnnotations = new SCNodeAnnotations(m_script.term("true"));
						nodeOnPath.getPayload().getAnnotations().put("SC", scAnnotations);
					}

					Term oldFormula = smtAnnotations.getAssertion();

					Const2VariableTermTransformer C2VTermTransformer = 
							new Const2VariableTermTransformer(scAnnotations.getConstants(),
							m_ConstantsToBoogieVar, nodeOnPath, m_script);
					Term interpolant = C2VTermTransformer.transform(interpolants[i]);
					
					s_logger.debug("REFINE: checking if assertion is strengthend " 
							+ oldFormula + " =>? " + interpolant);
					CFGExplicitNode dummyNode = new CFGExplicitNode(nodeOnPath, true);
					dummyNode.setAssertion(interpolant);
					CFGEdge dummyEdge = new CFGEdge(m_script, m_script.term("true"), nodeOnPath, dummyNode);
					LBool smtResult = dummyEdge.checkEdge(true);
					dummyEdge.deleteEdge();

					if (smtResult != LBool.UNSAT) {
						s_logger.debug("REFINE: strengthening assertion with " + interpolant);
						
						Term newFormula = Util.and(m_script,  oldFormula, interpolant);
						smtAnnotations.setAssertion(newFormula);	

						if(nodeOnPath.get_coveredNodes().size() > 0) {
							for(UnwindingNode coveredNode : nodeOnPath.get_coveredNodes()) {
								coveredNode.set_coveringNode(null);
								coveredNode.setCovered(false);
								if (coveredNode.isLeaf()) 
									m_openNodes.add(coveredNode);
								
								uncoverRec(coveredNode.getOutgoingEdges());
							}
							nodeOnPath.get_coveredNodes().clear();
							uncoverRec(nodeOnPath.getOutgoingEdges()); 
						}
					}
				}
				v.set_isLeaf(false);
				m_openNodes.remove(v);

				gw.writeGraphAsImage(m_graphroot, "graph_b_procProced" + countExpand++, m_openNodes);
			} 
			else {
				m_errorTrace = path;
				m_errorTraceFormulas = formulas;
				m_errorPath = new StringBuilder();
				m_errorPath.append("Satisfiable error path:\n");
				for(Term f : formulas) {
					m_errorPath.append(f.toString() + "\n");
				}
				m_programIncorrect = true;
			}
		}
	}
	
	private ArrayList<IElement> getPath(UnwindingNode v, ArrayList<IElement> path) {
		if(!(v instanceof UnwindingRoot)) {
			path.add(v);
			path.add(v.getIncomingEdges().get(0));
			return getPath((UnwindingNode)v.getIncomingNodes().get(0), path);	
		}
		else {
			path.add(v);
			Collections.reverse(path);
			return path;
		}
	}

	private void paper_CLOSE(UnwindingNode v) {
		noClose++;
		s_logger.debug("CLOSE has been called");

		if (v.isErrorLocation())
			return;
		
		ArrayList<UnwindingNode> predecessors = new ArrayList<UnwindingNode>(
				v.m_procRoot.getPreorder().subList(0,
					v.getIndexInPreorder()));

		for(UnwindingNode pred : predecessors) {
			if(pred.getOriginalCFGNode().equals(v.getOriginalCFGNode())) {
				paper_COVER(v, pred);
			}
		}
	}

	private void paper_COVER(UnwindingNode v, UnwindingNode w) {//w covert v ("v->w?")
		noCover++;
		if(!v.isCovered() && !w.isCovered()) {
			
			s_logger.debug("COVER: " + v + "->" + w + ": checking " 
					+ m_stripAnnotationsTT.transform(v.getSMTAnnotations().getAssertion()) +
					" =>? " + m_stripAnnotationsTT.transform(w.getSMTAnnotations().getAssertion()));
			assert (!v.isErrorLocation() && !w.isErrorLocation());
			
			CFGEdge coveringEdge = new CFGEdge(m_script, m_script.term("true"), v, w);
			LBool smtResult = coveringEdge.checkEdge(true);
			coveringEdge.deleteEdge();
			noImplicationChecks++;
			
			if (smtResult == LBool.UNSAT) { 
				s_logger.debug("COVER: implication valid -> covering..");
				
				v.set_coveringNode(w);
				w.get_coveredNodes().add(v);
				v.setCovered(true);
				m_openNodes.remove(v);
				coverRec(v.getOutgoingNodes());
			}
		}
	}

	/**
	 * for each given element recursively (going down) remove all covering edges connected to it
	 * and mark it as covered (by a node above of it by convention..)
	 */
	private void coverRec(List<INode> outgoingNodes) {
		if(outgoingNodes == null) return;
		for(INode iNode : outgoingNodes) {
			UnwindingNode unwNode = (UnwindingNode) iNode;
			
			unwNode.setCovered(true);
			m_openNodes.remove(unwNode);
			
			if(unwNode.get_coveringNode() != null) 
				unwNode.get_coveringNode().get_coveredNodes().remove(unwNode);
			
			for(UnwindingNode un : unwNode.get_coveredNodes()) {
				un.set_coveringNode(null);
				un.setCovered(false);				
				assert un.get_coveredNodes().size() == 0;
				
				if(un.isLeaf()) 
					m_openNodes.add(un);
				
				uncoverRec(un.getOutgoingEdges()); 
			}
			unwNode.get_coveredNodes().clear();
			unwNode.set_coveringNode(null);
			
			coverRec(unwNode.getOutgoingNodes());
		}
	}
	
	/**
	 * for each given element recursively (going down) set isCovered false and 
	 * clear the coveringNodes List 
	 */
	private void uncoverRec(List<IEdge> outgoingEdges) {
		if(outgoingEdges == null) return;
		for(IEdge iEdge : outgoingEdges) {
			UnwindingNode unwNode = (UnwindingNode) iEdge.getTarget();
			unwNode.setCovered(false);
			if(unwNode.isLeaf()) {
				m_openNodes.add(unwNode);	
			}
			if(unwNode.get_coveringNode() != null) {
				unwNode.set_coveringNode(null);
			}
			uncoverRec(unwNode.getOutgoingEdges());
		}
	}
	
	private void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
	}

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
	 * @return the root of the CFG.
	 */
	public INode getRoot(){
		return (INode) m_graphroot;
	}
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
			return o1.getIndexInPreorder() - o2.getIndexInPreorder();	
	}

}