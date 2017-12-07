package de.uni_freiburg.informatik.ultimate.automata.statefactory;

public class DummySemanticReducerFactory<STATE> implements ISemanticReducerFactory<STATE> {

	@Override
	public Iterable<STATE> filter(final Iterable<STATE> states) {
		return states;
	}

}
