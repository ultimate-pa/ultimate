package de.uni_freiburg.informatik.ultimate.plugins.generator.reimpact;

import java.util.HashSet;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
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
	
	boolean isPreCallNodeImportant = false;
	
	
	int m_preorderIndex = -1;
	
	
	public UnwindingNode(IPredicate predicate, ProgramPoint programPoint, 
			int preorderIndex) {
		super(predicate, programPoint);
		m_preorderIndex = preorderIndex;
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
	 */
	public boolean matchLocation(UnwindingNode other) {
		return other.getProgramPoint().equals(this.getProgramPoint());
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
