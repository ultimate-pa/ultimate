package local.stalin.automata.petrinet.jan;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;

import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.Place;

/**
 * @author Jan Mortensen
 *
 * @param <Symbol>
 * @param <Content>
 */
public class Transition<Symbol, Content> 
implements ITransition<Symbol, Content>{

	private Collection<Place<Symbol, Content>> m_successors;
	private Collection<Place<Symbol, Content>> m_predecessors;
	private Symbol m_symbol;
	
//	/**
//	 * Copy constructor.
//	 * 
//	 * @param transition The transition to copy.
//	 */
//	public Transition(ITransition<Symbol, Content> transition){
//	
//		super();
//		this.m_symbol = transition.getSymbol();
//			
//		m_successors = new HashSet<Place<Symbol, Content>>(
//				transition.getSuccessorPlaces());
//		m_predecessors = new HashSet<Place<Symbol, Content>>(
//				transition.getPredecessorPlaces());
//	}
	
	public Transition(Symbol symbol){
	
		super();
		this.m_symbol = symbol;
		m_successors = new HashSet<Place<Symbol, Content>>();
		m_predecessors = new HashSet<Place<Symbol, Content>>();
	}
	
	@Override
	public Collection<Place<Symbol, Content>> getPredecessors() {
		
		return m_predecessors;
	}

	@Override
	public Collection<Place<Symbol, Content>> getSuccessors() {
		
		return m_successors;
	}

	public void addPredecessorPlace(Place<Symbol, Content> predecessor) {
		
		this.m_predecessors.add(predecessor);	
	}

	public void addSuccessorPlace(Place<Symbol, Content> successor) {
		
		this.m_successors.add(successor);
	}

	@Override
	public Symbol getSymbol() {
		
		return m_symbol;
	}

	@Override
	public String toString(){
		
		return m_symbol.toString();
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public boolean equals(Object obj){
		
		if(!(obj instanceof Transition<?, ?>))
			return false;
		
		ITransition<Symbol, Content> event = (Transition<Symbol, Content>)obj;
		
		if(!(m_predecessors.equals(event.getPredecessors())))
			return false;
		
		if(!(m_successors.equals(event.getSuccessors())))
			return false;
		
		if(!(m_symbol.equals(event.getSymbol())))
			return false;
		
		return true;
	}

	@Override
	public int hashCode(){
		
		return 13 * m_predecessors.hashCode() +
			   7 * m_successors.hashCode() +
			   3 * m_symbol.hashCode();
	}
	
	public class Successors implements Iterable {

		@Override
		public Iterator iterator() {
			return m_successors.iterator();
		}
		
	}
}
