/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	MarkedTrace.java created on Mar 22, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * MarkedTrace
 *
 * @author Björn Buchhold
 *
 */
public class MarkedTrace {
	
	private List<IEdge> m_Trace;
	
	public enum MarkReason {info, error};
	
	private MarkReason m_MarkReason;
	
	private boolean m_OneNodeTrace;
	
	private GraphType m_GraphType;
	
	public MarkedTrace(List<IEdge> trace, GraphType gt, MarkReason markReason){
		this.m_Trace = trace;
		this.m_MarkReason = markReason;
		this.m_OneNodeTrace = false;
		this.m_GraphType = gt;
	}
	
	public MarkedTrace (INode node, GraphType gt, MarkReason markReason){
		this.m_Trace = new ArrayList<IEdge>();
		this.m_Trace.add(new Edge(node,  null));
		this.m_OneNodeTrace = true;
		this.m_GraphType = gt;
	}
	
	List<INode> getNodeSequence(){
		List<INode> sequence = new LinkedList<INode>();
		for (IEdge edge : m_Trace) {
			sequence.add(edge.getSource());
		}
		if(!m_OneNodeTrace){
			sequence.add(m_Trace.get(m_Trace.size()-1).getTarget());
		}
		return sequence;
	}
	
	/**
	 * getter for field m_MarkReason
	 * @return the m_MarkReason
	 */
	public MarkReason getMarkReason() {
		return this.m_MarkReason;
	}
	
	public GraphType getGraphType() {
		return this.m_GraphType;
	}
	
}
