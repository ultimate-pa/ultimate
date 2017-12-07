package de.uni_freiburg.informatik.ultimate.automata.statefactory;

import java.util.List;
import java.util.Set;

public class DummySemanticReducerFactory<STATE, LETTER> implements ISemanticReducerFactory<STATE, LETTER> {

	@Override
	public Iterable<STATE> filter(final Iterable<STATE> states) {
		return states;
	}

	@Override
	public STATE getOptimalDestination(final List<STATE> src, final LETTER letter, final Set<STATE> dest) {
		// TODO Auto-generated method stub
		return null;
	}

}
