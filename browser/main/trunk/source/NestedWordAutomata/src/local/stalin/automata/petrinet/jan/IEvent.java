package local.stalin.automata.petrinet.jan;

import java.util.Collection;

import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.Place;

public interface IEvent<Symbol, Content> 
extends Comparable<IEvent<Symbol, Content>>{
	
	public void addPredecessorCondition(
			ICondition<Symbol, Content> predecessor);
	public void addSuccessorCondition(ICondition<Symbol, Content> successor);
	
	public Collection<Place<Symbol, Content>> 
		getByLocalConfigurationRepresentedMarking();

	public ITransition<Symbol, Content> getTransition();
	public Collection<ICondition<Symbol, Content>> getPredecessorConditions();
	public Collection<ICondition<Symbol, Content>> getSuccessorConditions();
	
	public int sizeOfLocalConfiguration();
	
	/**
	 * Calculates the marking represented my the local configuration of this
	 * event. For a correct calculation call this method after adding all
	 * predecessor and successor conditions.
	 */
	public void calculateRepresentedMarking();
	public Collection<IEvent<Symbol, Content>> getLocalConfiguration();
	
	/**
	 * 
	 * @param b Sets the reachable marking found by this event.
	 */
	public void leadsToRepresentationOfAcceptingMarking(
			Collection<ICondition<Symbol, Content>> marking);
	
	/**
	 * 
	 * @return A reachable accepting marking or null if no one found by this 
	 * 		   event.  
	 */
	public Collection<ICondition<Symbol, Content>> 
		getRepresentatedOfAcceptingMarking();
}
