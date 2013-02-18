package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;

public class Place<S,C> implements Serializable {
	private static final long serialVersionUID = -4577818193149596161L;

	private final int m_HashCode;
	
	static int s_SerialNumberCounter = 0;
	
	private final C m_Content;
	private final ArrayList<ITransition<S,C>> m_Predecessors;
	private final ArrayList<ITransition<S,C>> m_Successors;
	
	private final int m_SerialNumber = s_SerialNumberCounter++;
	
	
	
	public Place(C content) {
		this.m_Content = content;
		this.m_Predecessors = new ArrayList<ITransition<S,C>>();
		this.m_Successors = new ArrayList<ITransition<S,C>>();
		m_HashCode = computeHashCode();
	}
	
	public C getContent() {
		return m_Content;
	}
	
	public Collection<ITransition<S, C>> getPredecessors() {
		return m_Predecessors;
	}
	
	public Collection<ITransition<S, C>> getSuccessors() {
		return m_Successors;
	}
	
	public void addPredecessor(ITransition<S,C> transition) {
		m_Predecessors.add(transition);
	}
	
	public void addSuccessor(ITransition<S,C> transition) {
		m_Successors.add(transition);
	}
	
	@Override
	public String toString() {
		return "#"+ m_SerialNumber + "#" + String.valueOf(m_Content);
	}

	@Override
	public int hashCode() {
		return m_HashCode;
	}
	
	public int computeHashCode() {
		return m_SerialNumber;
	}
	
}
