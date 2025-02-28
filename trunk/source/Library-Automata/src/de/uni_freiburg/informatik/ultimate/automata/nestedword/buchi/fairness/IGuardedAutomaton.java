package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public interface IGuardedAutomaton<LETTER, STATE, GUARD> {
	Set<STATE> getInitialStates();

	boolean isAccepting(STATE state);

	Set<LETTER> getAlphabet();

	Set<Triple<LETTER, GUARD, STATE>> getSuccessors(STATE state, LETTER letter);
}
