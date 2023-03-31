package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Accepts<LETTER, STATE, CRSF extends IStateFactory<STATE>> extends GeneralOperation<LETTER, STATE, CRSF> {
	private final boolean mResult;

	public Accepts(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton,
			final NestedLassoWord<LETTER> word) {
		super(services);
		// TODO: Could we use another type of lasso-words here instead?
		if (!word.getStem().hasEmptyNestingRelation() || !word.getLoop().hasEmptyNestingRelation()) {
			throw new AssertionError("Rabin automata cannot handle calls/returns.");
		}
		mResult = computeResult(automaton, word.getStem().asList(), word.getLoop().asList());
	}

	private boolean computeResult(final IRabinAutomaton<LETTER, STATE> automaton, final List<LETTER> stem,
			final List<LETTER> loop) {

		final HashSet<STATE> currentStateSet = new HashSet<>();
		automaton.getInitialStates().forEach(x -> currentStateSet.add(x));

		for (final LETTER letter : stem) {
			final HashSet<STATE> temp = new HashSet<>();
			if (currentStateSet.isEmpty()) {
				return false;
			}
			for (final STATE currentState : currentStateSet) {
				for (final OutgoingInternalTransition<LETTER, STATE> possibleTransition : automaton
						.getSuccessors(currentState, letter)) {
					temp.add(possibleTransition.getSucc());
				}

				if (temp.isEmpty()) {
					return false;
				}
				currentStateSet.clear();
				currentStateSet.addAll(temp);
			}
		}

		int loopIndex = 0;
		final HashSet<Pair<Integer, HashSet<STATE>>> uniqueSituations = new HashSet<>();
		final HashSet<Pair<Integer, HashSet<STATE>>> knownSituations = new HashSet<>();
		final HashSet<Pair<Integer, STATE>> exploredAcceptingSituations = new HashSet<>();
		do {
			knownSituations.add(new Pair<>(loopIndex, currentStateSet));
			final HashSet<STATE> temp = new HashSet<>();
			for (final STATE state : currentStateSet) {
				for (final OutgoingInternalTransition<LETTER, STATE> possibleTransition : automaton.getSuccessors(state,
						loop.get(loopIndex))) {
					final STATE successor = possibleTransition.getSucc();
					if (automaton.isAccepting(successor)
							&& !exploredAcceptingSituations.contains(new Pair<>(loopIndex, successor))) {
						for (final OutgoingInternalTransition<LETTER, STATE> acceptorTransition : automaton
								.getSuccessors(successor, loop.get((loopIndex + 1) % loop.size()))) {

							if (!automaton.isFinite(acceptorTransition.getSucc())
									&& hasOmegaPathTo(automaton, acceptorTransition.getSucc(), successor, loop,
											((loopIndex + 2) % loop.size()), new HashSet<>())) {
								return true;
							}
							exploredAcceptingSituations.add(new Pair<>(loopIndex, successor));

						}

					}
				}
			}
			currentStateSet.clear();
			currentStateSet.addAll(temp);
			uniqueSituations.add(new Pair<>(loopIndex, currentStateSet));
			loopIndex = (loopIndex + 1) % loop.size();

		} while (!uniqueSituations.equals(knownSituations));

		return false;
	}

	// Should use DFS to explore if there is at least one loop from proposedEndpoint to itself with input of
	// omegaWord^omega.
	private boolean hasOmegaPathTo(final IRabinAutomaton<LETTER, STATE> automaton, final STATE start, final STATE goal,
			final List<LETTER> omegaWord, final int wordIndex, final HashSet<Pair<Integer, STATE>> knownSituations) {
		final HashSet<Pair<Integer, STATE>> uniqueSituations = new HashSet<>();
		uniqueSituations.addAll(knownSituations);
		final STATE current = start;
		do {
			for (final OutgoingInternalTransition<LETTER, STATE> possibleTransition : automaton.getSuccessors(current,
					omegaWord.get(wordIndex))) {
				final STATE succ = possibleTransition.getSucc();
				if (!automaton.isFinite(succ)) {
					if (goal.equals(succ)) {
						return true;
					}
					uniqueSituations.add(new Pair<>(wordIndex, succ));
					if (hasOmegaPathTo(automaton, succ, goal, omegaWord, ((wordIndex + 1) % omegaWord.size()),
							uniqueSituations)) {
						return true;
					}
				}
			}
		} while (uniqueSituations != knownSituations);
		return false;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}
}
