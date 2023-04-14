package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class EagerRabinAutomaton<LETTER, STATE> implements IRabinAutomaton<LETTER, STATE> {

	private final Set<LETTER> mAlphabet;
	private final Set<STATE> mStates;
	private final Set<STATE> mInitialStates;
	private final Set<STATE> mAcceptingStates;
	private final Set<STATE> mFiniteStates;
	private final NestedMap2<STATE, LETTER, Set<STATE>> mTransitions;

	/**
	 * @param automaton
	 *            The automaton that should be optimized
	 *
	 *            This automaton constructs the minimal Automaton containing all reachable transitions and states from
	 *            the initials of the given IRabinAutomaton. Finite States are allowed.
	 */
	public EagerRabinAutomaton(final IRabinAutomaton<LETTER, STATE> automaton) {
		this(automaton, true);
	}

	/**
	 * @param automaton
	 *            The automaton that should be optimized
	 * @param allowFinites
	 *            if set to false all finite states and transitions to/from them are ignored
	 *
	 *            This automaton constructs the minimal Automaton containing all reachable transitions and states from
	 *            the initials of the given IRabinAutomaton
	 */
	public EagerRabinAutomaton(final IRabinAutomaton<LETTER, STATE> automaton, final boolean allowFinites) {

		mInitialStates = new HashSet<>();
		mStates = new HashSet<>();
		mTransitions = new NestedMap2<>();
		mAlphabet = new HashSet<>();
		mFiniteStates = new HashSet<>();
		mAcceptingStates = new HashSet<>();

		automaton.getInitialStates().forEach(x -> mInitialStates.add(x));

		final ArrayList<STATE> currentStateSet = new ArrayList<>();
		final ArrayList<STATE> temp = new ArrayList<>();

		if (!allowFinites) {
			mInitialStates.removeIf(x -> automaton.isFinite(x));
		}

		currentStateSet.addAll(mInitialStates);

		while (!currentStateSet.isEmpty()) {

			mStates.addAll(currentStateSet);

			for (final STATE currentState : currentStateSet) {
				if (automaton.isFinite(currentState)) {
					mFiniteStates.add(currentState);
				} else if (automaton.isAccepting(currentState)) {
					mAcceptingStates.add(currentState);
				}

				for (final OutgoingInternalTransition<LETTER, STATE> transition : automaton
						.getSuccessors(currentState)) {
					if (allowFinites || !automaton.isFinite(transition.getSucc())) {

						final LETTER letter = transition.getLetter();
						mAlphabet.add(letter);
						if (!mTransitions.containsKey(currentState, letter)) {
							mTransitions.put(currentState, letter, new HashSet<>());
						}
						mTransitions.get(currentState, transition.getLetter()).add(transition.getSucc());

						temp.add(transition.getSucc());
					}
				}
			}
			currentStateSet.clear();
			temp.removeAll(mStates);
			currentStateSet.addAll(temp);
			temp.clear();
		}
	}

	@Override
	public Set<LETTER> getAlphabet() {

		return mAlphabet;
	}

	@Override
	public int size() {

		return mStates.size();
	}

	@Override
	public String sizeInformation() {
		// TODO Implement more information on return.
		return "Number of states: " + size();
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> getInitialStates() {

		return mInitialStates;
	}

	@Override
	public boolean isInitial(final STATE state) {

		return mInitialStates.contains(state);
	}

	@Override
	public boolean isAccepting(final STATE state) {

		return mAcceptingStates.contains(state);
	}

	@Override
	public boolean isFinite(final STATE state) {

		return mFiniteStates.contains(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		final Set<OutgoingInternalTransition<LETTER, STATE>> result = new HashSet<>();
		if (mTransitions.get(state) == null) {
			return result;
		}
		for (final Entry<LETTER, Set<STATE>> entry : mTransitions.get(state).entrySet()) {
			for (final STATE succ : entry.getValue()) {
				result.add(new OutgoingInternalTransition<>(entry.getKey(), succ));
			}
		}
		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		final Set<OutgoingInternalTransition<LETTER, STATE>> result = new HashSet<>();
		if (mTransitions.get(state, letter) == null) {
			return result;
		}
		for (final STATE succ : mTransitions.get(state, letter)) {

			result.add(new OutgoingInternalTransition<>(letter, succ));

		}
		return result;
	}

	public EagerRabinAutomaton<LETTER, STATE> getStemlessNonFiniteAutomaton() {
		final RabinAutomaton<LETTER, STATE> stemlessAutomaton = new RabinAutomaton<>(mAlphabet, mStates,
				mAcceptingStates, mAcceptingStates, mFiniteStates, mTransitions);
		final EagerRabinAutomaton<LETTER, STATE> result = new EagerRabinAutomaton<>(stemlessAutomaton, false);
		return result;

	}

}
