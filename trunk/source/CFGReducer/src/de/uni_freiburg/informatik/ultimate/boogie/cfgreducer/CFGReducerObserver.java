package de.uni_freiburg.informatik.ultimate.boogie.cfgreducer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.CFGNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.CFGRootAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.PayloadModifier;
import de.uni_freiburg.informatik.ultimate.boogie.cfgreducer.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.cfgreducer.preferences.PreferenceValues;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * This class reduces the CFG by merging nodes, which do form a loopless sequence in the original CFG.
 * It also shifts the assumptions to the succeeding edges of a node.
 * 
 */

public class CFGReducerObserver implements IUnmanagedObserver {
	
	private static final Boolean				s_debugMessages		= false;
	private static Logger						s_Logger			= UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private Script 								m_Script;
	private static CFGExplicitNode				m_graphroot;
	private boolean								m_idTagEdges		= false;
	private boolean								m_mergeParallelEdges= false;
	private boolean								m_reduceGraph		= false;
	private boolean								m_madeChanges		= false;
//	private SubstituteTermTransformer			m_subTermTransformer= new SubstituteTermTransformer();
	
	/**
	 * 
	 * @return the root of the CFG.
	 */
	public IElement getRoot(){
		if(s_debugMessages) CFGReducerObserver.s_Logger.debug("Returning graphroot!!");
		return CFGReducerObserver.m_graphroot;
	}
	
	@Override
	public boolean process(IElement node) {
	
		IEclipsePreferences prefs = ConfigurationScope.INSTANCE.getNode(Activator.PLUGIN_ID);
		m_reduceGraph = !prefs.getBoolean(PreferenceValues.NAME_REDUCEGRAPH, PreferenceValues.VALUE_REDUCEGRAPH_DEFAULT);
		m_idTagEdges = prefs.getBoolean(PreferenceValues.NAME_IDTAGEDGES, PreferenceValues.VALUE_IDTAGEDGES_DEFAULT);
		m_mergeParallelEdges= prefs.getBoolean(PreferenceValues.NAME_MERGEPARALLELEDGES, PreferenceValues.VALUE_MERGEPARALLELEDGES_DEFAULT);
		
		s_Logger.info("Reduce graph is set to " + m_reduceGraph);
		s_Logger.info("Id Tags are set to " + m_idTagEdges);
		s_Logger.info("Merge parallel edges is set to " + m_mergeParallelEdges);
		
		if (node instanceof CFGNode) {
			m_madeChanges = true;
			CFGNode root	= (CFGNode) node;
			CFGRootAnnotations rootAnnotations = (CFGRootAnnotations)root.getPayload().getAnnotations().get("CFGBuilder");
			m_Script 			= rootAnnotations.getScript();
			m_graphroot		= new CFGExplicitNode(m_Script, m_Script.term("true"));
			m_graphroot.resetCounter();
			
			m_graphroot.setPayload(PayloadModifier.copyPayload(root.getPayload()));
			s_Logger.info("BMdata:(CFGReducer) >(1)PreNode#: " + countNodes(root));
			
			// to clear all static data from cfg edges
			new CFGEdge(m_Script, m_Script.term("true"), null, null).clearEdgeStaticData();
			
			
			for (int i = 0; i < root.getOutgoingNodes().size(); i++) {
				INode n = root.getOutgoingNodes().get(i);
				CFGExplicitNode procNode = processProcedure((CFGNode) n);
				new CFGEdge(m_Script, m_Script.term("true"), m_graphroot, procNode);
				s_Logger.info("Initial Node# of " + 
						procNode.getPayload().getName() + ": " + countNodes(procNode));
				if (m_reduceGraph){
					do{
//						m_madeChanges = m_madeChanges || initStep1(procNode);
//						s_Logger.info("-->> " + countNodes(procNode));
					}while(initStep1(procNode));
				}
				s_Logger.info("Final Node# : " + procNode.getPayload().getName() 
						+ ": " + countNodes(procNode));
			}

			s_Logger.info("BMdata:(CFGReducer) >(2)PostNode#: " + initializeFormulas());
		} else if (node instanceof CFGExplicitNode && m_reduceGraph) {
//			m_graphroot	= (CFGExplicitNode)node;
//			s_Logger.info("BMdata:(IterativeReduction) > PreNode#: " + countNodes(m_graphroot));
//			m_Script 	= m_graphroot.getScript();
//			m_graphroot.resetCounter();
//			
//			for (IEdge tmp : m_graphroot.getOutgoingEdges()) {
//				CFGEdge edge = (CFGEdge)tmp;
//				do{
//					m_visited.clear();
//				}while(reduce_Node((CFGExplicitNode)edge.getTarget()));
//			}
//			s_Logger.info("BMdata:(IterativeReduction) > PostNode#: " + countNodes(m_graphroot));
//			s_Logger.info(m_graphroot.hashCode());
//			s_Logger.info(m_graphroot.hashCode());
			throw new UnsupportedOperationException("CFGReducer only works on CFGNodes!");
		} else {
			throw new UnsupportedOperationException("CFGReducer only works on CFGNodes!");
		}
		return false;
	}

	public CFGExplicitNode processProcedure(CFGNode procNode) {
		CFGNodeAnnotations cfgNodeAnnotations = procNode.getCFGAnnotations();
		CFGExplicitNode result = new CFGExplicitNode(m_Script,
				cfgNodeAnnotations.getAssertion());
		result.getPayload().getAnnotations().put(
				"procedure", cfgNodeAnnotations);
		result.getPayload().setLocation(procNode.getPayload().getLocation());
		result.getPayload().setName(procNode.getPayload().getName());
		
		HashMap<BoogieVar, TermVariable> invars		= cfgNodeAnnotations.getInVars();
		HashMap<BoogieVar, TermVariable> outvars	= cfgNodeAnnotations.getOutVars();
		HashSet<TermVariable> vars					= cfgNodeAnnotations.getVars();
		
		Node2ExplicitNodeConverter n2ExNConverter = new Node2ExplicitNodeConverter();
		for (INode node : procNode.getOutgoingNodes()) {
			CFGExplicitNode explNode = n2ExNConverter.convert((CFGNode) node, m_Script, m_idTagEdges);
			CFGEdge edge = new CFGEdge(m_Script, cfgNodeAnnotations.getAssumption(), result, explNode);
			edge.getSMTAnnotations().setInVars(invars);
			edge.getSMTAnnotations().setOutVars(outvars);
			edge.getSMTAnnotations().setVars(vars);
			if (m_idTagEdges) {
				edge.makeId();
			}
		}
		result.getSMTAnnotations().setVars(vars);
		return result;
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
	
	private boolean initStep1(CFGExplicitNode node) {
		return new ReductionStep().start(node);
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return m_madeChanges;
	}
	
	private int countNodes(INode root){
		return collectNodes(root).size();
	}
	
	private int initializeFormulas() {
		s_Logger.info("Starting initialization of formulas...");
		ArrayList<INode> nodes = 
				collectNodes(m_graphroot);
		for(INode iNode: nodes) {
			CFGExplicitNode node = (CFGExplicitNode) iNode; 
			node.applySubstitution();
		}
		s_Logger.info("... done.");
		return nodes.size();
	}
	
	private ArrayList<INode> collectNodes(INode root){
		ArrayList<INode> searchStack = new ArrayList<INode>();
		for (IEdge e: root.getOutgoingEdges()) {
			searchStack.add(e.getTarget());
		}
		
		int i = 0;
		// if the search stack still holds edges that might lead to an error continue...
		while(i < searchStack.size()) {
			// get the current node which will be expanded
			INode node = searchStack.get(i);
			// run through all descendants... 
			List<INode> children = node.getOutgoingNodes();
			if (children != null){
				for(INode n: node.getOutgoingNodes()) {
					// check if descendant has already been visited by another path(shorter path by construction of BFS)
					if (!searchStack.contains(n)) {
						// append new edge to search stack since descendant has not been visited yet
						searchStack.add(n);
					}
				}
			}
			i++;
		}
		return searchStack;
	}
}
