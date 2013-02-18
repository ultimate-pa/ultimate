package de.uni_freiburg.informatik.ultimate.plugins.generator.reimpact;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class UnwindingNode extends RIAnnotatedProgramPoint {

	boolean m_isLeaf = true;
	boolean m_isProcRoot = false;
	boolean m_isCovered = false;
	UnwindingNode m_coveringNode;
	HashSet<UnwindingNode> m_coveredNodes = new HashSet<UnwindingNode>();
	
	Stack<UnwindingNode> m_preCallNodeStack = new Stack<UnwindingNode>();
	
	int m_preorderIndex = -1;
	
	
	public UnwindingNode(IPredicate predicate, ProgramPoint programPoint, 
			Stack<UnwindingNode> preCallNodeStack, int preorderIndex) {
		super(predicate, programPoint);
		m_preorderIndex = preorderIndex;
		m_preCallNodeStack = preCallNodeStack;
	}
	
	/**
	 * constructor for the procedure root node
	 */
	public UnwindingNode(IPredicate predicate, ProgramPoint programPoint, boolean isProcRoot) {
		super(predicate, programPoint);
		assert isProcRoot;
		m_isProcRoot = true;
		m_preorderIndex = 0;
	}

	/*
	 * check for this and another node whether they have the same location in
	 * the original RCFG _and_ the node before the closest preceding call of each
	 * match
	 * (this is a necessary precondition for covering in ReImpact on recursive programs) 
	 */
	public boolean matchLocation(UnwindingNode other) {
		boolean preCallsMatch = false;
		if (this.getPreCallNode() == null && other.getPreCallNode() == null)
			preCallsMatch = true;
		else if (this.getPreCallNode() != null && other.getPreCallNode() != null)
			preCallsMatch = other.getPreCallNode().getProgramPoint()
				.equals(this.getPreCallNode().getProgramPoint());
		
		return other.getProgramPoint().equals(this.getProgramPoint()) &&
				preCallsMatch;	
	}
	
	public boolean isPreCallNode() {
		boolean toReturn = false;
		for (INode inode : this.getOutgoingNodes()) {
			if (toReturn == true)
				break;
			else
				toReturn = getOutgoingCodeBlockOf((RIAnnotatedProgramPoint) inode)
					instanceof Call;
		}
		return toReturn;
	}

	public UnwindingNode getPreCallNode() {
		return m_preCallNodeStack.isEmpty() ? null : m_preCallNodeStack.peek();
	}

	public int getPreOrderIndex() {
		return m_preorderIndex;
	}
	
	public boolean isCovered() {
		return m_isCovered;
	}
	
	public void setIsLeaf(boolean isLeaf) {
		m_isLeaf = isLeaf;
	}
	
	public boolean isLeaf() {
		return m_isLeaf;
	}
	
	public String toString() {
		return super.toString() + ":" + m_preorderIndex;
	}
}
