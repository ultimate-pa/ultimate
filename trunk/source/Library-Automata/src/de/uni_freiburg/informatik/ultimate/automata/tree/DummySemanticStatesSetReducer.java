package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.Collection;

public class DummySemanticStatesSetReducer<STATE> implements SemanticStatesSetReducer<STATE> {

	@Override
	public Collection<STATE> filter(final Collection<STATE> states) {
		return states;
	}

}
