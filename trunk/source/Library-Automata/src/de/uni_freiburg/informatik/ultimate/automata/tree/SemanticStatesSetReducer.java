package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.Collection;

public interface SemanticStatesSetReducer<STATE> {
	
	/**
	 * Filter out semantically redundant states.
	 * @param states A collection of states.
	 * @return A collection of filtered states
	 */
	Collection<STATE> filter(final Collection<STATE> states);
}
