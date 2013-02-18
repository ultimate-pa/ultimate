package local.stalin.automata.petrinet.jan;

import java.util.Collection;
import java.util.HashSet;

import local.stalin.automata.petrinet.Place;

public class Condition<Symbol, Content> implements ICondition<Symbol, Content>{
	
	private Place<Symbol, Content> m_place;
	private IEvent<Symbol, Content> m_predecessor;
	private Collection<IEvent<Symbol, Content>> m_successors;
	
	public Condition(Place<Symbol, Content> place){
		
		this.m_successors = new HashSet<IEvent<Symbol, Content>>();
		this.m_place = place;
	}
	
	/**
	 * Returns the predecessor event of this condition or null, if the
	 * condition is related to a start place of the corresponding petri net.
	 * 
	 * @return The predecessor event or null.
	 */
	@Override
	public IEvent<Symbol, Content> getPredecessorEvent(){
		return m_predecessor;
	}

	@Override
	public Place<Symbol, Content> getPlace(){
		return m_place;
	}

	@Override
	public Collection<IEvent<Symbol, Content>> getSuccessorEvents() {
		return m_successors;
	}

	@Override
	public void addSuccessorEvent(IEvent<Symbol, Content> predecessor) {
		
		this.m_successors.add(predecessor);
	}
	
	@Override
	public void setPredecessorEvent(IEvent<Symbol, Content> predecessor) {
		
		this.m_predecessor = predecessor;	
	}
	
	@Override
	public String toString(){
		
		return "(" + m_place.getContent().toString() + ", " + hashCode() + ")";
	}
}
