package local.stalin.automata.petrinet.jan;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import local.stalin.automata.petrinet.Place;

public interface IOccurrenceNet<Symbol, Content> {

	public ICondition<Symbol, Content> 
		addCondition(Place<Symbol, Content> relatedPlace);
	public void addEvent(IEvent<Symbol, Content> event);
	public void setInitialConditions(
			Collection<ICondition<Symbol, Content>> condition);
	
	public Collection<ICondition<Symbol, Content>> getConditions();
	public Collection<IEvent<Symbol, Content>> getEvents();
	
	/**
	 * @param condition1 The first condition.
	 * @param condition2 The second condition.
	 * @return Weather the two given conditions are in co relation.
	 */
	public boolean inCoRelation(ICondition<Symbol, Content> condition1, 
								ICondition<Symbol, Content> condition2);
	
	/**
	 * @param event The event leading to the representation of an accepting 
	 * 				marking.
	 */
	public void setToRepresentationOfAcceptingMarkingLeadingEvent(
			IEvent<Symbol, Content> event);
	
	/**
	 * @return The saved event which leads to the representation of an accepting
	 * 		   marking.
	 */
	public IEvent<Symbol, Content> 
		getToRepresentationOFAcceptingMarkingLeadingEvent();
	
	public boolean isInOccurenceNet(IEvent<Symbol, Content> event);
	
	/**
	 * @return A map which maps markings of the petri net to events which
	 * 		   represent this marking.
	 */
	public Map<Collection<Place<Symbol, Content>>, 
			   Collection<IEvent<Symbol, Content>>> getMarkings2Events();
	
	/**
	 * @return A map which maps places of the petri net to a set of conditions
	 * 		   that are labeled with this place.
	 */
	public Map<Place<Symbol, Content>, Collection<ICondition<Symbol, Content>>>
		getPlace2Conditions();
	
	public boolean isCutOffEvent(IEvent<Symbol, Content> event);
	public Collection<IEvent<Symbol, Content>> getCutOffEvents();
	
	/**
	 * Returns a collection of all conditions related to the given place, or 
	 * null if no condition exists.
	 * 
	 * @param place A place of the petri net.
	 * 
	 * @return A collection of all conditions related to the given place, or 
	 * 		   null if no condition exists.
	 */
	public Collection<ICondition<Symbol, Content>> 
		getConditions(Place<Symbol, Content> place);
	
	public Collection<ICondition<Symbol,Content>> getInitialConditions();
	
	public List<Collection<Place<Symbol, Content>>> getAcceptingRun();
}
