package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

public class InhibitorTransition<S, C> extends Transition<S, C> {
	private static final long serialVersionUID = 933451776613619705L;

	private final Collection<Place<S, C>> m_Inhibitors;

	public InhibitorTransition(S symbol, Collection<Place<S, C>> predecessors,
			Collection<Place<S, C>> inhibitors,
			Collection<Place<S, C>> successors, int totalOrderID) {
		super(symbol, predecessors, successors, totalOrderID);
		this.m_Inhibitors = inhibitors;
	}

	public Collection<Place<S, C>> getInhibitors() {
		return m_Inhibitors;
	}

}
