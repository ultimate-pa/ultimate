package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Accepts<LETTER, STATE, CRSF extends IStateFactory<STATE>> extends GeneralOperation<LETTER, STATE, CRSF> {
	private final boolean mResult;

	public Accepts(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton,
			final NestedLassoWord<LETTER> word) throws AutomataOperationCanceledException {
		super(services);
		// TODO: Could we use another type of lasso-words here instead?
		if (!word.getStem().hasEmptyNestingRelation() || !word.getLoop().hasEmptyNestingRelation()) {
			throw new AssertionError("Rabin automata cannot handle calls/returns.");
		}
		mResult = computeResult(automaton, word.getStem().asList(), word.getLoop().asList());
	}

	/*
	 * computes paths to accepting states with iterative letter evaluation and returns true iff if one of them has a
	 * valid infinite loop returns false if no new situations with letter state pairs are found iff no true value was
	 * returned first
	 */
	private boolean computeResult(final IRabinAutomaton<LETTER, STATE> automaton, final List<LETTER> stem,
			final List<LETTER> loop) throws AutomataOperationCanceledException {

		final ArrayList<STATE> currentStateSet = stemEvaluation(automaton, stem);
		final ArrayList<STATE> temp = new ArrayList<>();
		int loopIndex = 0;
		final HashSet<Pair<Integer, STATE>> uniqueSituations = new HashSet<>();
		final HashSet<Pair<Integer, STATE>> visitedSituations = new HashSet<>();
		currentStateSet.forEach(x -> uniqueSituations.add(new Pair<>(0, x)));
		do {
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(getClass());
			}
			if (currentStateSet.isEmpty()) {
				return false;
			}
			for (final STATE state : currentStateSet) {

				if (automaton.isAccepting(state) && !automaton.isFinite(state)
						&& !visitedSituations.contains(new Pair<>(loopIndex, state))
						&& hasLoop(automaton, state, loop, loopIndex)) {
					return true;
				}

				visitedSituations.add(new Pair<>(loopIndex, state));
				for (final OutgoingInternalTransition<LETTER, STATE> possibleTransition : automaton.getSuccessors(state,
						loop.get(loopIndex))) {
					final STATE sucessor = possibleTransition.getSucc();
					if (!visitedSituations.contains(new Pair<>((loopIndex + 1) % loop.size(), sucessor))) {
						temp.add(sucessor);
					}
				}
			}
			currentStateSet.clear();
			currentStateSet.addAll(temp);
			temp.clear();
			loopIndex = (loopIndex + 1) % loop.size();
			for (final STATE state : currentStateSet) {
				uniqueSituations.add(new Pair<>(loopIndex, state));
			}

		} while (!uniqueSituations.equals(visitedSituations));

		return false;

	}

	/*
	 * Produces a new set of starting states that is valid after stem is read. Works similar to a NFA interpreter.
	 */

	private ArrayList<STATE> stemEvaluation(final IRabinAutomaton<LETTER, STATE> automaton, final List<LETTER> stem) {
		final ArrayList<STATE> currentStateSet = new ArrayList<>();
		automaton.getInitialStates().forEach(x -> currentStateSet.add(x));
		final ArrayList<STATE> temp = new ArrayList<>();
		for (final LETTER letter : stem) {
			if (currentStateSet.isEmpty()) {
				break;
			}
			for (final STATE currentState : currentStateSet) {
				for (final OutgoingInternalTransition<LETTER, STATE> possibleTransition : automaton
						.getSuccessors(currentState, letter)) {
					temp.add(possibleTransition.getSucc());
				}

			}
			currentStateSet.clear();
			currentStateSet.addAll(temp);
			temp.clear();
		}
		return currentStateSet;
	}

	/*
	 * Tests if a loop exists from state to itself with input loop
	 */
	private boolean hasLoop(final IRabinAutomaton<LETTER, STATE> automaton, final STATE start, final List<LETTER> loop,
			final int loopIndex) throws AutomataOperationCanceledException {

		final ArrayList<STATE> currentStateSet = new ArrayList<>();
		final ArrayList<STATE> temp = new ArrayList<>();
		int localLoopIndex = loopIndex;
		final HashSet<Pair<Integer, STATE>> uniqueSituations = new HashSet<>();
		final HashSet<Pair<Integer, STATE>> visitedSituations = new HashSet<>();

		currentStateSet.add(start);
		uniqueSituations.add(new Pair<>(loopIndex, start));

		do {
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(getClass());
			}
			if (currentStateSet.isEmpty()) {
				return false;
			}

			for (final STATE state : currentStateSet) {
				for (final OutgoingInternalTransition<LETTER, STATE> possibleTransition : automaton.getSuccessors(state,
						loop.get(localLoopIndex))) {
					final STATE sucessor = possibleTransition.getSucc();
					if (!automaton.isFinite(sucessor)) {
						if (loopIndex == (localLoopIndex + 1) % loop.size() && sucessor.equals(start)) {
							return true;
						}
						if (!visitedSituations.contains(new Pair<>((localLoopIndex + 1) % loop.size(), sucessor))) {
							temp.add(sucessor);
						}
					}
				}
				visitedSituations.add(new Pair<>(localLoopIndex, state));
			}
			currentStateSet.clear();
			currentStateSet.addAll(temp);
			temp.clear();

			localLoopIndex = (localLoopIndex + 1) % loop.size();
			for (final STATE state : currentStateSet) {
				uniqueSituations.add(new Pair<>(localLoopIndex, state));
			}
		} while (!uniqueSituations.equals(visitedSituations));

		return false;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}
}
