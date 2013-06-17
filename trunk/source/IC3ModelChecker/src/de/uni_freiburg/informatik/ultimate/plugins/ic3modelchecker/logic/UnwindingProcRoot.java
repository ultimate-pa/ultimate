/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;

/**
 * @author nutz
 *
 */
public class UnwindingProcRoot extends UnwindingNode {

	private static final long serialVersionUID = 4212252432287810076L;
	
	private ArrayList<UnwindingNode> m_allNodesInPreorder;
//	private HashMap<CFGExplicitNode, ArrayList<UnwindingNode>> m_locationToPreorder;
	
	public UnwindingProcRoot(CFGExplicitNode origNode) {
		super(origNode, true, null);
		m_allNodesInPreorder = new ArrayList<UnwindingNode>();
//		m_locationToPreorder = new HashMap<CFGExplicitNode, ArrayList<UnwindingNode>>();
		m_procRoot = this;
	}
	
//	public UnwindingProcRoot(Script script, Term formula) {
////		m_theory = theory;
////		m_formula = formula;
//		// * taken from CFGExplicitNode:
//		super(script, formula);
//		m_allNodesInPreorder = new ArrayList<UnwindingNode>();
//		m_procRoot = this;
//	}
	
//	/**
//	 * call copy constructor 
//	 */
//	public UnwindingProcRoot(CFGExplicitNode root, boolean useSsa) {
//		super(root, useSsa);
//	}

	/*
	 * the procedure root keeps track of the preorder of the nodes - has to be updated when 
	 * a node is added to an unwinding 
	 */
	public void addToPreorder(UnwindingNode n) {
		m_allNodesInPreorder.add(n);
	}
	
//	/*
//	 * the procedure root keeps track of the preorder of the nodes - has to be updated when 
//	 * a node is added to an unwinding
//	 */
//	public void addToPreorder(UnwindingNode un, CFGExplicitNode cn) {
//		if(!m_locationToPreorder.containsKey(cn)) 			
//			m_locationToPreorder.put(cn, new ArrayList<UnwindingNode>());
//			
//		m_locationToPreorder.get(cn).add(un);
//	}

	/*
	 * get the List representing the Preordering of the Nodes in the Unwinding
	 */
	public ArrayList<UnwindingNode> getPreorder() {
		return m_allNodesInPreorder;
	}

//	/**
//	 * @return the m_locationToPreorder
//	 */
//	public HashMap<CFGExplicitNode, ArrayList<UnwindingNode>> getLocationToPreorder() {
//		return m_locationToPreorder;
//	}
}
