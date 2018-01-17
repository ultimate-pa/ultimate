package de.uni_freiburg.informatik.ultimate.automata.statefactory;

import java.util.List;
import java.util.Set;

public class DummySemanticReducerFactory<STATE, LETTER> implements ISemanticReducerFactory<STATE, LETTER> {

	@Override
	public Iterable<STATE> filter(final Iterable<STATE> states) {
		return states;
	}

	@Override
	public Iterable<STATE> getOptimalDestination(Iterable<STATE> states, List<STATE> src, LETTER letter,
			Set<STATE> dest) {
		return null;
	}

}
