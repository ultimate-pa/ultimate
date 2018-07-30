package de.uni_freiburg.informatik.ultimate.automata.statefactory;

import java.util.List;

public class DummySemanticReducerFactory<STATE, LETTER> implements ISemanticReducerFactory<STATE, LETTER> {

	@Override
	public Iterable<STATE> filter(final Iterable<STATE> states) {
		return states;
	}

	@Override
	public Iterable<STATE> getOptimalDestination(final Iterable<STATE> states, final List<STATE> src,
			final LETTER letter, final Iterable<STATE> dest) {
		return dest;
	}

}
