package local.stalin.automata.petrinet.julian;

import java.util.Collection;
import java.util.Collections;

import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.Place;

public class Transition<S,C> implements ITransition<S,C> {
	private final S m_Symbol;
	private final Collection<Place<S,C>> m_Predecessors;
	private final Collection<Place<S,C>> m_Successors;
	
	public Transition(S symbol, 
			Collection<Place<S,C>> predecessors,
			Collection<Place<S,C>> successors) {
		m_Symbol = symbol;
		m_Predecessors = Collections.unmodifiableCollection(predecessors);
		m_Successors = Collections.unmodifiableCollection(successors);
	}
	
	@Override
	public S getSymbol() {
		return m_Symbol;
	}

	@Override
	public Collection<Place<S,C>> getPredecessors() {
		return m_Predecessors;
	}

	@Override
	public Collection<Place<S,C>> getSuccessors() {
		return m_Successors;
	}


}
