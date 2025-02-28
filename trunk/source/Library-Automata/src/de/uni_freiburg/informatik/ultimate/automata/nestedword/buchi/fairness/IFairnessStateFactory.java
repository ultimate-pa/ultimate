package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public interface IFairnessStateFactory<STATE, STATE2, LETTER, GUARD> {
	STATE combineStates(STATE state, STATE2 state2);

	Pair<STATE, STATE2> getOriginalStates(STATE combinedState);

	LETTER combineGuard(LETTER letter, GUARD guard, Set<LETTER> enabledAction);

	boolean isTrivial(GUARD guard);

	boolean isInfeasible(LETTER letter);

	Set<LETTER> getEnabledActions(STATE state);
}
