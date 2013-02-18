package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

public class Transition<S, C> implements ITransition<S, C>, Serializable,
		Comparable<Transition<S, C>> {
	private static final long serialVersionUID = 5948089529814334197L;

	private final int m_HashCode;
	private final S m_Symbol;
	private final Collection<Place<S, C>> m_Predecessors;
	private final Collection<Place<S, C>> m_Successors;

	private final int m_TotalOrderID;

	public Transition(S symbol, Collection<Place<S, C>> predecessors,
			Collection<Place<S, C>> successors, int totalOrderID) {
		m_Symbol = symbol;
		m_Predecessors = Collections
				.unmodifiableList((List<Place<S, C>>) predecessors);
		m_Successors = Collections
				.unmodifiableList((List<Place<S, C>>) successors);
		m_HashCode = computeHashCode();
		m_TotalOrderID = totalOrderID;
	}

	@Override
	public S getSymbol() {
		return m_Symbol;
	}

	@Override
	public Collection<Place<S, C>> getPredecessors() {
		return m_Predecessors;
	}

	@Override
	public Collection<Place<S, C>> getSuccessors() {
		return m_Successors;
	}

	@Override
	public int hashCode() {
		return m_HashCode;
	}

	public int computeHashCode() {
		return 13 * m_Predecessors.hashCode() + 7 * m_Successors.hashCode() + 3
				* m_Symbol.hashCode();
	}

	@Override
	public String toString() {
		return m_Symbol.toString()+"["+m_TotalOrderID+"]";
	}

	public int getTotalOrderID() {
		return m_TotalOrderID;
	}

	@Override
	public int compareTo(Transition<S, C> o) {
		return m_TotalOrderID - o.m_TotalOrderID;
	}

}
