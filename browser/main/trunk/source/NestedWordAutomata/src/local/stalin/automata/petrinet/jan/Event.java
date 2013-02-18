package local.stalin.automata.petrinet.jan;

import java.util.Collection;
import java.util.HashSet;

import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.Place;

public class Event<Symbol, Content> implements IEvent<Symbol, Content>{
	
	private ITransition<Symbol, Content> m_transition;
	private Collection<ICondition<Symbol, Content>> m_predecessors;
	private Collection<ICondition<Symbol, Content>> m_successors;
	private Collection<ICondition<Symbol, Content>> 
		m_leadsToRepresentationOfAcceptingMarking;
	private Collection<IEvent<Symbol, Content>> m_localConfiguration;
	private Collection<Place<Symbol, Content>> m_representedMarking; 
	
	public Event(ITransition<Symbol, Content> transition, 
				 Collection<ICondition<Symbol, Content>> predecessors){
		
		m_predecessors = new HashSet<ICondition<Symbol, Content>>();
		m_successors = new HashSet<ICondition<Symbol, Content>>();
		m_localConfiguration = new HashSet<IEvent<Symbol, Content>>();
		m_representedMarking = new HashSet<Place<Symbol, Content>>();
		
		this.m_transition = transition;
		this.m_predecessors.addAll(predecessors);
		
		calculateLocalConfiguration();
		
		 m_leadsToRepresentationOfAcceptingMarking = null;
	}

	@Override
	public Collection<ICondition<Symbol, Content>> getPredecessorConditions() {
		
		return m_predecessors;
	}

	@Override
	public ITransition<Symbol, Content> getTransition() {

		return m_transition;
	}

	@Override
	public Collection<ICondition<Symbol, Content>> getSuccessorConditions() {
		
		return m_successors;
	}

	@Override
	public void addPredecessorCondition(
			ICondition<Symbol, Content> predecessor) {
		
		this.m_predecessors.add(predecessor);
	}

	@Override
	public void addSuccessorCondition(ICondition<Symbol, Content> successor) {
		
		this.m_successors.add(successor);
	}
 
	@Override
	public int compareTo(IEvent<Symbol, Content> o) {
	
		int result;
		
		if(this.m_localConfiguration.size() > 
		   o.sizeOfLocalConfiguration())
			result = 1;
		else if(this.m_localConfiguration.size() < 
				o.sizeOfLocalConfiguration())
			result = -1;
		else 
			result = 0;
		
		return result;	
	}

	@Override
	public int sizeOfLocalConfiguration() {

		return m_localConfiguration.size();
	}
	
	private void calculateLocalConfiguration(){
		
		m_localConfiguration.add(this);
		
		for(ICondition<Symbol, Content> condition : m_predecessors){
			
			if(condition.getPredecessorEvent() != null){
			
				m_localConfiguration.addAll(condition.getPredecessorEvent().
						getLocalConfiguration());
			}
		}
	}
	
	@Override
	public Collection<IEvent<Symbol, Content>> getLocalConfiguration(){
		return m_localConfiguration;
	}

	@Override
	public void calculateRepresentedMarking() {

		m_representedMarking =
			new HashSet<Place<Symbol, Content>>();
		
		for(ICondition<Symbol, Content> condition : m_predecessors)
			if(condition.getPredecessorEvent() != null)
				m_representedMarking.addAll(
						condition.getPredecessorEvent().
						getByLocalConfigurationRepresentedMarking());
		
		//This for loop is a not yet tested bugfix by Matthias
		for(ICondition<Symbol, Content> predCond : m_predecessors) {
			IEvent<Symbol, Content> predEvent = predCond.getPredecessorEvent();
			if(predEvent != null) {
				for (ICondition<Symbol, Content> predCondOfPredEvent : 
					predEvent.getPredecessorConditions()){
					m_representedMarking.remove(predCondOfPredEvent.getPlace());
				}
			}
		}
			
		for(ICondition<Symbol, Content> condition : m_predecessors)
			m_representedMarking.remove(condition.getPlace());
		
		for(ICondition<Symbol, Content> condition : m_successors)
			m_representedMarking.add(condition.getPlace());
		
	}
	
	@Override
	public Collection<Place<Symbol, Content>> 
		getByLocalConfigurationRepresentedMarking() {

		return m_representedMarking;
	}
	
	/**
	 * @return The cut which represents an accepting marking or null if no one 
	 * is represented.
	 */
	@Override
	public void leadsToRepresentationOfAcceptingMarking(
		Collection<ICondition<Symbol, Content>> marking) {

		m_leadsToRepresentationOfAcceptingMarking = marking;
	}

	@Override
	public Collection<ICondition<Symbol, Content>> 
		getRepresentatedOfAcceptingMarking() {
		
		return m_leadsToRepresentationOfAcceptingMarking;
	}
	
	@Override
	public String toString(){
	
		String result = "Event labeled with (" + m_transition + 
						"): Pre=(";
		
		for(ICondition<Symbol, Content> pre : m_predecessors)
			result += pre.getPlace() + " ";
		
		result = result.trim()+") Succ=(";
		for(ICondition<Symbol, Content> succ : m_successors)
			result += succ.getPlace() + " ";
		
		result = result.trim() + ")";
	
		return result;
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public boolean equals(Object obj){
		
		if(!(obj instanceof Event<?, ?>))
			return false;
		
		IEvent<Symbol, Content> event = (Event<Symbol, Content>)obj;
		
		if(!(m_predecessors.equals(event.getPredecessorConditions())))
			return false;
		
		if(!(m_successors.equals(event.getSuccessorConditions())))
			return false;
		
		if(!(m_transition.equals(event.getTransition())))
			return false;
		
		return true;
	}
	
	@Override
	public int hashCode(){
		
		return 7 * m_predecessors.hashCode() + 
			   3 * m_successors.hashCode() +
			   11 * m_transition.hashCode();
	} 
}