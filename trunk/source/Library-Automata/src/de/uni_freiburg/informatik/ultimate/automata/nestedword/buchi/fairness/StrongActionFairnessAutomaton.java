package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class StrongActionFairnessAutomaton<LETTER> implements IGuardedAutomaton<LETTER, Integer, Set<LETTER>> {
	private final Set<LETTER> mAlphabet;
	private final Set<LETTER> mFairActions;

	public StrongActionFairnessAutomaton(final Set<LETTER> alphabet, final Set<LETTER> fairActions) {
		mAlphabet = alphabet;
		mFairActions = fairActions;
	}

	@Override
	public Set<Integer> getInitialStates() {
		return Set.of(0);
	}

	@Override
	public boolean isAccepting(final Integer state) {
		return state > 0;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public Set<Triple<LETTER, Set<LETTER>, Integer>> getSuccessors(final Integer state, final LETTER letter) {
		if (state == 0) {
			if (mFairActions.contains(letter)) {
				return Set.of(new Triple<>(letter, Set.of(), 1));
			}
			return Set.of(new Triple<>(letter, Set.of(), 0), new Triple<>(letter, mFairActions, 2));
		}
		if (state == 1) {
			return Set.of(new Triple<>(letter, Set.of(), 0));
		}
		if (state == 2 && !mFairActions.contains(letter)) {
			return Set.of(new Triple<>(letter, mFairActions, 2));
		}
		return Set.of();
	}

	@Override
	public Set<Set<LETTER>> getGuards(final LETTER letter) {
		return mFairActions.contains(letter) ? Set.of(Set.of()) : Set.of(Set.of(), mFairActions);
	}
}
