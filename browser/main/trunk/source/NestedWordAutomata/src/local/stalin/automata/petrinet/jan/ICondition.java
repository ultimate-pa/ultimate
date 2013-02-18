package local.stalin.automata.petrinet.jan;

import java.util.Collection;

import local.stalin.automata.petrinet.Place;

public interface ICondition<Symbol, Content>{

	public void addSuccessorEvent(IEvent<Symbol, Content> successor);
	public void setPredecessorEvent(IEvent<Symbol, Content> predecessor);
	
	public Place<Symbol, Content> getPlace();
	public IEvent<Symbol, Content> getPredecessorEvent();
	public Collection<IEvent<Symbol, Content>> getSuccessorEvents();
}
