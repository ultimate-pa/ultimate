package de.uni_freiburg.informatik.ultimate.plugins.generator.reimpact;

import java.util.HashSet;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

/* Covering condition:
 * - program location matches
 * - 
 */
public class UnwindingNode extends RIAnnotatedProgramPoint {

	private static final long serialVersionUID = 961856940528940879L;
	boolean m_isLeaf = true;
	boolean m_isProcRoot = false;
	boolean m_isCovered = false;
	UnwindingNode m_coveringNode;
	HashSet<UnwindingNode> m_coveredNodes = new HashSet<UnwindingNode>();
	
	Stack<UnwindingNode> m_preCallNodeStack;
	boolean isPreCallNodeImportant = false;
	
	int m_preorderIndex = -1;
	
	
	public UnwindingNode(IPredicate predicate, ProgramPoint programPoint, 
			Stack<UnwindingNode> preCallNodeStack, int preorderIndex) {
		super(predicate, programPoint);
		//assert preorderIndex > 0 || preorderIndex == -5;
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
		m_preCallNodeStack = new Stack<UnwindingNode>();
	}

	/**
	 * check the location conditions for a covering, "this" is the covered node,
	 * the parameter is the covering one.
	 * - check if the isPreCallNodeImportant-flag is set for the covering node,
	 *  in case see if the PreCallNodes match
	 * - check if the Program locations are the same
	 */
	public boolean matchLocationForCovering(UnwindingNode coveringTarget) {
		if (coveringTarget.isPreCallNodeImportant) {
			boolean preCallsMatch = false;
			if (this.getPreCallNode() == null && coveringTarget.getPreCallNode() == null)
				preCallsMatch = true;
			else if (this.getPreCallNode() != null && coveringTarget.getPreCallNode() != null)
				preCallsMatch = coveringTarget.getPreCallNode().equals(this.getPreCallNode());

			return coveringTarget.getProgramPoint().equals(this.getProgramPoint()) &&
					preCallsMatch;	
		} else {
			return coveringTarget.getProgramPoint().equals(this.getProgramPoint());
		}
	}
	
	public boolean isPreCallNode() {
		boolean toReturn = false;
		for (RIAnnotatedProgramPoint app : this.getOutgoingNodes()) {
			if (toReturn == true)
				break;
			else
				toReturn = this.getOutgoingEdgeLabel(app) instanceof Call;
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
	
	public boolean isPreCallNodeImportant() {
		return isPreCallNodeImportant;
	}

	public void setPreCallNodeImportant(boolean isPreCallNodeImportant) {
		this.isPreCallNodeImportant = isPreCallNodeImportant;
	}

	public String toString() {
		return super.toString() + ":" + m_preorderIndex;
	}
}
