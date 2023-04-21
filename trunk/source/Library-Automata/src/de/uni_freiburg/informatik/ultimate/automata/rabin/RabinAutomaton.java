package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class RabinAutomaton<LETTER, STATE> implements IRabinAutomaton<LETTER, STATE> {

	private final Set<LETTER> mAlphabet;
	private final Set<STATE> mStates;
	private final Set<STATE> mInitialStates;
	private final Set<STATE> mAcceptingStates;
	private final Set<STATE> mFiniteStates;
	private final NestedMap2<STATE, LETTER, Set<STATE>> mTransitions;

	/**
	 * A Rabin Automaton explicitly defined by the parameters
	 *
	 * @param alphabet
	 *            The valid input characters for this automaton (should be a superset of the characters in transitions)
	 * @param states
	 *            The valid states of the automaton (should be a superset of the states in initialStates,
	 *            acceptingStates, finiteStates and transitions)
	 * @param initialStates
	 *            The states that are active when no letter/word has been read
	 * @param acceptingStates
	 *            States that when infinitely often visited lead to the acceptance of the input
	 * @param finiteStates
	 *            States that can only be visited a finite amount of times, iff the automaton accepts
	 * @param transitions
	 *            The transitions from one state to another for a one letter input
	 */
	public RabinAutomaton(final Set<LETTER> alphabet, final Set<STATE> states, final Set<STATE> initialStates,
			final Set<STATE> acceptingStates, final Set<STATE> finiteStates,
			final NestedMap2<STATE, LETTER, Set<STATE>> transitions) {
		mAlphabet = alphabet;
		mStates = states;
		mInitialStates = initialStates;
		mAcceptingStates = acceptingStates;
		mFiniteStates = finiteStates;
		mTransitions = transitions;
	}

	public Set<STATE> getStates() {
		return mStates;
	}

	public Set<STATE> getAcceptingStates() {
		return mAcceptingStates;
	}

	public Set<STATE> getFiniteStates() {
		return mFiniteStates;
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
		if (mTransitions.get(state) == null) {
			return Set.of();
		}
		final Set<OutgoingInternalTransition<LETTER, STATE>> result = new HashSet<>();
		for (final Entry<LETTER, Set<STATE>> entry : mTransitions.get(state).entrySet()) {
			for (final STATE succ : entry.getValue()) {
				result.add(new OutgoingInternalTransition<>(entry.getKey(), succ));
			}
		}
		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		if (mTransitions.get(state, letter) == null) {
			return Set.of();
		}

		final Set<OutgoingInternalTransition<LETTER, STATE>> result = new HashSet<>();
		for (final STATE succ : mTransitions.get(state, letter)) {

			result.add(new OutgoingInternalTransition<>(letter, succ));

		}
		return result;
	}

	public NestedMap2<STATE, LETTER, Set<STATE>> getTransitions() {
		return mTransitions;
	}

}
