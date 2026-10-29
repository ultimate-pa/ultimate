package de.uni_freiburg.informatik.ultimate.automata.afa;

import java.util.Set;

public interface IAlternatingFiniteAutomaton<L, S> {

	Set<L> getAlphabet();

	int size();

	Iterable<S> getInitialStates();

	boolean isInitial(final S state);

	boolean isFinal(final S state);

	Bdd<S> getSuccessors(final S state, final L letter);

}
