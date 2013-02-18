package local.stalin.automata.petrinet;

import java.util.ArrayList;
import java.util.Collection;

public class Place<S,C> {
	private final C m_Content;
	private final ArrayList<ITransition<S,C>> m_Predecessors;
	private final ArrayList<ITransition<S,C>> m_Successors;
	
	public Place(C content) {
		this.m_Content = content;
		this.m_Predecessors = new ArrayList<ITransition<S,C>>();
		this.m_Successors = new ArrayList<ITransition<S,C>>();
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
		return String.valueOf(m_Content);
	}
	
}
