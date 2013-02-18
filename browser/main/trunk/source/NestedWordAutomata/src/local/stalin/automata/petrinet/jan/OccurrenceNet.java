package local.stalin.automata.petrinet.jan;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.automata.petrinet.Place;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;

public class OccurrenceNet<Symbol, Content> 
implements IOccurrenceNet<Symbol, Content>{
	
	protected static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private Collection<ICondition<Symbol, Content>> m_conditions;
	private Collection<IEvent<Symbol, Content>> m_events;
	private Map<Collection<Place<Symbol, Content>>,
		    	Collection<IEvent<Symbol, Content>>> m_markings2events;
	private Map<Place<Symbol, Content>, 
				Collection<ICondition<Symbol, Content>>> m_place2conditions;
	private Collection<IEvent<Symbol, Content>> m_cutOffEvents;
	protected Collection<ICondition<Symbol, Content>> m_initialConditions;
	protected IEvent<Symbol, Content> 
		m_toRepresentationOfAcceptingMarkingLeadingEvent;
	private Map<ICondition<Symbol, Content>, 
				Collection<ICondition<Symbol, Content>>>
					m_coRelations;
	
	public OccurrenceNet(){
		
		m_conditions = new HashSet<ICondition<Symbol, Content>>();
		m_events = new HashSet<IEvent<Symbol, Content>>();
		m_markings2events = new HashMap<Collection<Place<Symbol, Content>>, 
	  		  							Collection<IEvent<Symbol, Content>>>();
		m_place2conditions = new HashMap<Place<Symbol, Content>, 
									Collection<ICondition<Symbol, Content>>>();
		m_cutOffEvents = new HashSet<IEvent<Symbol, Content>>();
		m_initialConditions = new HashSet<ICondition<Symbol, Content>>();
		m_coRelations = new HashMap<ICondition<Symbol, Content>, 
									Collection<ICondition<Symbol, Content>>>();
	}
	
	@Override
	public ICondition<Symbol, Content> 
		addCondition(Place<Symbol, Content> relatedPlace){
		
		ICondition<Symbol, Content> newCondition = 
			new Condition<Symbol, Content>(relatedPlace);
		this.m_conditions.add(newCondition);
		
		if(m_place2conditions.get(relatedPlace) == null)
			m_place2conditions.put(relatedPlace, 
								new HashSet<ICondition<Symbol, Content>>());
		m_place2conditions.get(relatedPlace).add(newCondition);
				
		return newCondition;
	}
	
	@Override
	public void addEvent(IEvent<Symbol, Content> event){
		
		this.m_events.add(event);
		
		updateConditions(event);
		
		if(m_markings2events.get(
				event.getByLocalConfigurationRepresentedMarking()) == null)
			m_markings2events.put(
					event.getByLocalConfigurationRepresentedMarking(), 
					new HashSet<IEvent<Symbol, Content>>());
		m_markings2events.get(
				event.getByLocalConfigurationRepresentedMarking()).
				add(event);
		
		if(calculateIfCutOffEvent(event))
			m_cutOffEvents.add(event);
	}

	@Override
	public Collection<ICondition<Symbol, Content>> getConditions() {
		return m_conditions;
	}
	

	@Override
	public Collection<IEvent<Symbol, Content>> getEvents() {
		return m_events;
	}

	@Override
	public boolean isInOccurenceNet(IEvent<Symbol, Content> event) {
		
		boolean result = false;
		
		for(IEvent<Symbol, Content> checkedEvent : m_events)
			if(checkedEvent.getPredecessorConditions().containsAll(
					event.getPredecessorConditions()) && 
					event.getPredecessorConditions().containsAll(
					checkedEvent.getPredecessorConditions()))
				result = true;
		
		return result;
	}
	
	@Override
	public void setInitialConditions(
			Collection<ICondition<Symbol, Content>> conditions){
		 
		m_initialConditions.addAll(conditions);
		
		
		//Save that all conditions related to a place in the initial marking
		//is pairwise in co relation.
		for(ICondition<Symbol, Content> condition1 : m_initialConditions){
			
			for(ICondition<Symbol, Content> condition2 : m_initialConditions){
	
				setCoRelation(condition1, condition2);
			}
		}
	}
	
	private void setCoRelation(ICondition<Symbol, Content> condition1,
							   ICondition<Symbol, Content> condition2){
		
		if(condition1.hashCode() > condition2.hashCode()){
			
			if(m_coRelations.get(condition1) == null){
				
				m_coRelations.put(condition1, 
								  new HashSet<ICondition<Symbol, Content>>());
			}
			
			m_coRelations.get(condition1).add(condition2);
		}
		else if(condition1.hashCode() < condition2.hashCode()){

			if(m_coRelations.get(condition2) == null){
				
				m_coRelations.put(condition2, 
								  new HashSet<ICondition<Symbol, Content>>());
			}
			
			m_coRelations.get(condition2).add(condition1);	
		}
		else{
			
			if(m_coRelations.get(condition2) == null){
			
				m_coRelations.put(condition2, 
								  new HashSet<ICondition<Symbol, Content>>());
			}
			
			m_coRelations.get(condition2).add(condition1);
			
			if(m_coRelations.get(condition1) == null){
				
				m_coRelations.put(condition1, 
								  new HashSet<ICondition<Symbol, Content>>());
			}
			
			m_coRelations.get(condition1).add(condition2);
		}
	}
	
	@Override
	public boolean inCoRelation(ICondition<Symbol, Content> condition1, 
								ICondition<Symbol, Content> condition2){

		if(condition1.hashCode() > condition2.hashCode()){
			
			if(m_coRelations.get(condition1) == null){
				
				return false;
			}
			else{
				
				return m_coRelations.get(condition1).contains(condition2);
			}
		}
		else if(condition1.hashCode() < condition2.hashCode()){
		
			if(m_coRelations.get(condition2) == null){
				
				return false;
			}
			else{
				
				return m_coRelations.get(condition2).contains(condition1);
			}
		}
		else{
			
			if(m_coRelations.get(condition2) == null && 
			   m_coRelations.get(condition1) == null){
				return false;
			}
			else if(m_coRelations.get(condition2) != null){
				
				return m_coRelations.get(condition2).contains(condition1);
			}
			else if(m_coRelations.get(condition1) != null){
				
				return m_coRelations.get(condition1).contains(condition2);
			}
			else{
				return m_coRelations.get(condition1).contains(condition2) ||
					   m_coRelations.get(condition2).contains(condition1);
			}
		}
	} 
	
	/**
	 * Returns a set of conditions which are in co relation to the given
	 * condition.
	 */
	private Collection<ICondition<Symbol, Content>> 
		getConditionsInCoRelation(ICondition<Symbol, Content> condition){
		
		Collection<ICondition<Symbol, Content>> coConditions =
			new HashSet<ICondition<Symbol, Content>>();
		
		for(ICondition<Symbol, Content> c : m_conditions){
			
			if(m_coRelations.get(c) != null && 
					m_coRelations.get(c).contains(condition)){
				
				coConditions.add(c);
			}
		}
		
		coConditions.addAll(m_coRelations.get(condition));
		
		return coConditions; 
	}
	
	private void updateConditions(IEvent<Symbol, Content> event){

		//update successor edges of the inserted conditions 
		for(ICondition<Symbol, Content> pre : event.getPredecessorConditions()){
			
			pre.addSuccessorEvent(event);
		}

		//update predecessor edges of the inserted conditions
		for(ICondition<Symbol, Content> succ : event.getSuccessorConditions()){
			
			succ.setPredecessorEvent(event);
		}
		
		//update map of co relations
		for(ICondition<Symbol, Content> successorCondition : 
			event.getSuccessorConditions()){

			//Use this map to save conditions temporarily 
			m_coRelations.put(successorCondition, 
							  new HashSet<ICondition<Symbol, Content>>());
	
			for(ICondition<Symbol, Content> predecessorCondition : 
				event.getPredecessorConditions()){
				
				m_coRelations.get(successorCondition).addAll(
						getConditionsInCoRelation(predecessorCondition));
			}
			
			for(ICondition<Symbol, Content> predecessorCondition : 
				event.getPredecessorConditions()){
				
				m_coRelations.get(successorCondition).retainAll(
						getConditionsInCoRelation(predecessorCondition));
			}
			
			m_coRelations.get(successorCondition).removeAll(
					event.getPredecessorConditions());
	
			//Save conditions with the save method to make sure all relations
			//are saved on the right position.
			HashSet<ICondition<Symbol, Content>> temp = 
				new HashSet<ICondition<Symbol, Content>>(
						m_coRelations.get(successorCondition));
			m_coRelations.get(successorCondition).clear();
			for(ICondition<Symbol, Content> con1 : temp)
				setCoRelation(con1, successorCondition);
			
		}
	
		//Every new conditions is pairwise in co relation to all other just 
		//added conditions.
		for(ICondition<Symbol, Content> condition1 : 
			event.getSuccessorConditions()){
			
			for(ICondition<Symbol, Content> condition2 : 
				event.getSuccessorConditions()){
				
				setCoRelation(condition1, condition2);
			}
		}
	}
	
	@Override
	public String toString(){
	
		return "OccurrenceNet: \n" + 
			"Conditions: " + m_conditions + "\n" + 
			"Events :" + m_events;
	}

	@Override
	public Map<Collection<Place<Symbol, Content>>, 
			   Collection<IEvent<Symbol, Content>>> getMarkings2Events() {
		
		return m_markings2events;
	}

	@Override
	public Map<Place<Symbol, Content>, 
			   Collection<ICondition<Symbol, Content>>> getPlace2Conditions() {
	
		return m_place2conditions;
	}

	@Override
	public Collection<IEvent<Symbol, Content>> getCutOffEvents() {

		return m_cutOffEvents;
	}

	@Override
	public boolean isCutOffEvent(IEvent<Symbol, Content> event) {

		return m_cutOffEvents.contains(event);
	}
	
	/**
	 * Calculates if a given event is a cut-of event.
	 */
	private boolean calculateIfCutOffEvent(IEvent<Symbol, Content> event){
		
		boolean isCutOffEvent = false;
		
		if(m_markings2events.get(
				event.getByLocalConfigurationRepresentedMarking()) != null){
			for(IEvent<Symbol, Content> testedEvent : m_markings2events.get(
					event.getByLocalConfigurationRepresentedMarking())){
				if(testedEvent.sizeOfLocalConfiguration() < 
						event.sizeOfLocalConfiguration() && 
				   !testedEvent.equals(event)){
				
					isCutOffEvent = true;
					break;
				}
			}
		}
		
		return isCutOffEvent;
	}

	@Override
	public Collection<ICondition<Symbol, Content>> getConditions(
			Place<Symbol, Content> place) {
		
		return m_place2conditions.get(place);
	}

	@Override
	public Collection<ICondition<Symbol, Content>> getInitialConditions() {

		return m_initialConditions;
	}

	@Override
	public void setToRepresentationOfAcceptingMarkingLeadingEvent(
		IEvent<Symbol, Content> event) {

		m_toRepresentationOfAcceptingMarkingLeadingEvent = event;
	}

	@Override
	public IEvent<Symbol, Content> 
		getToRepresentationOFAcceptingMarkingLeadingEvent() {
	
		return m_toRepresentationOfAcceptingMarkingLeadingEvent;
	}

	@Override
	public List<Collection<Place<Symbol, Content>>> getAcceptingRun() {
		
		if(m_toRepresentationOfAcceptingMarkingLeadingEvent == null){
			
			return null;
		}
		else{
			
			List<Collection<Place<Symbol, Content>>> acceptingRun = 
				new ArrayList<Collection<Place<Symbol, Content>>>();
			Collection<ICondition<Symbol, Content>> marking = 
				new HashSet<ICondition<Symbol, Content>>();
			marking.addAll(m_initialConditions);
			
			PriorityQueue<IEvent<Symbol, Content>> eventsToFire = 
				new PriorityQueue<IEvent<Symbol,Content>>();
			Collection<IEvent<Symbol, Content>> temp = 
				new HashSet<IEvent<Symbol, Content>>();
			for(ICondition<Symbol, Content> condition : 
				m_toRepresentationOfAcceptingMarkingLeadingEvent.
					getRepresentatedOfAcceptingMarking())
				temp.addAll(
						condition.getPredecessorEvent().
							getLocalConfiguration());
			eventsToFire.addAll(temp);
			
			String acceptingWord = "";
			
			while(!eventsToFire.isEmpty()){
				
				addMarkingToRun(acceptingRun, marking);
				
				acceptingWord += 
					eventsToFire.peek().getTransition().getSymbol() + " ";
				
				fireEvent(eventsToFire.poll(), marking);
			}
			
			addMarkingToRun(acceptingRun, marking);
			
			s_Logger.info("Accepting Word: " + acceptingWord);
			
			return acceptingRun;
		}
	}
	
	
	
	public NestedRun<Symbol, Content> getAcceptedWord() {
		
		if(m_toRepresentationOfAcceptingMarkingLeadingEvent == null){
			
			return null;
		}
		else{
			
			
			List<Collection<Place<Symbol, Content>>> acceptingRun = 
				new ArrayList<Collection<Place<Symbol, Content>>>();
			Collection<ICondition<Symbol, Content>> marking = 
				new HashSet<ICondition<Symbol, Content>>();
			marking.addAll(m_initialConditions);
			
			PriorityQueue<IEvent<Symbol, Content>> eventsToFire = 
				new PriorityQueue<IEvent<Symbol,Content>>();
			Collection<IEvent<Symbol, Content>> temp = 
				new HashSet<IEvent<Symbol, Content>>();
			for(ICondition<Symbol, Content> condition : 
				m_toRepresentationOfAcceptingMarkingLeadingEvent.
					getRepresentatedOfAcceptingMarking())
				temp.addAll(
						condition.getPredecessorEvent().
							getLocalConfiguration());
			eventsToFire.addAll(temp);
			
			String acceptingWord = "";
			NestedWord<Symbol> nw = new NestedWord<Symbol>((Symbol[]) new Object[0]);
			NestedRun<Symbol, Content> nr = new NestedRun<Symbol, Content>(null);
			
			while(!eventsToFire.isEmpty()){
				
				addMarkingToRun(acceptingRun, marking);
				
				acceptingWord += 
					eventsToFire.peek().getTransition().getSymbol() + " ";
				NestedWord<Symbol> nw1 = new NestedWord<Symbol>(eventsToFire.peek().getTransition().getSymbol());
				nw.concatenate(nw1);
				NestedRun<Symbol, Content> nr1 = new NestedRun<Symbol, Content>(null, eventsToFire.peek().getTransition().getSymbol(), NestedWord.INTERNAL_POSITION, null);
				nr = nr.concatenate(nr1);
				
				fireEvent(eventsToFire.poll(), marking);
			}
			
			addMarkingToRun(acceptingRun, marking);
			
			s_Logger.info("Accepting Word: " + acceptingWord);
			
			return nr;
		}
	}
	
	
	
	
	
	protected List<Collection<Place<Symbol, Content>>>
		addMarkingToRun(List<Collection<Place<Symbol, Content>>> markings,
				   Collection<ICondition<Symbol, Content>> marking){
		
		Collection<Place<Symbol, Content>> newMarking = 
			new HashSet<Place<Symbol, Content>>();
		
		for(ICondition<Symbol, Content> condition : marking)
			newMarking.add(condition.getPlace());
		
		markings.add(newMarking);
		
		return markings;
	}
	
	protected Collection<ICondition<Symbol, Content>>
	fireEvent(IEvent<Symbol, Content> event,
	 Collection<ICondition<Symbol, Content>> marking){
		
		 marking.addAll(event.getSuccessorConditions());
		 marking.removeAll(event.getPredecessorConditions());
		 
		 return marking;
	 }
}