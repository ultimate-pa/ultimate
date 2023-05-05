package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * class to lazyly construct the union of two Rabin automata
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letter
 * @param <STATE>
 *            type of state
 */
public class RabinUnion<LETTER, STATE> implements IRabinAutomaton<LETTER, STATE> {

	private final IRabinAutomaton<LETTER, STATE> mFirstAutomaton;
	private final IRabinAutomaton<LETTER, STATE> mSecondAutomaton;
	private final IBlackWhiteStateFactory<STATE> mFactory;
	private final HashSet<STATE> mInitialStates = new HashSet<>();
	private final HashSet<STATE> mFiniteStates = new HashSet<>();
	private final HashSet<STATE> mAcceptingStates = new HashSet<>();
	// 1 ~ firstAutomaton ~ Black, 0 ~ secondAutomaton ~ White
	HashMap<STATE, Pair<Boolean, STATE>> mAutomatonMap = new HashMap<>();

	/**
	 * implementation that lazyly constructs the union of two Rabin automata
	 *
	 * @param firstAutomaton
	 *            first Rabin automaton to unite
	 * @param secondAutomaton
	 *            second Rabin automaton to unite
	 * @param factory
	 *            some BlackWhiteStateFactory for STATE
	 */
	public RabinUnion(final IRabinAutomaton<LETTER, STATE> firstAutomaton,
			final IRabinAutomaton<LETTER, STATE> secondAutomaton, final IBlackWhiteStateFactory<STATE> factory) {
		mFirstAutomaton = firstAutomaton;
		mSecondAutomaton = secondAutomaton;
		mFactory = factory;

		mFirstAutomaton.getInitialStates().forEach(x -> mInitialStates.add(getUnionState(x, true)));
		mSecondAutomaton.getInitialStates().forEach(x -> mInitialStates.add(getUnionState(x, false)));
	}

	@Override
	public Set<LETTER> getAlphabet() {
		assert mFirstAutomaton.getAlphabet().equals(mSecondAutomaton.getAlphabet());

		return mFirstAutomaton.getAlphabet();
	}

	@Override
	public int size() {

		return mFirstAutomaton.size() + mSecondAutomaton.size();
	}

	@Override
	public String sizeInformation() {

		return "Number of states: " + size() + "\n" + "of these there are: " + mFirstAutomaton.size()
				+ " from firstAutomaton and: " + mSecondAutomaton.size() + " from secondAutomaton";
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

		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();

		final Pair<Boolean, STATE> originalStateInformation = mAutomatonMap.get(state);

		if (Boolean.TRUE.equals(originalStateInformation.getFirst())) {
			mFirstAutomaton.getSuccessors(originalStateInformation.getSecond()).forEach(
					x -> result.add(new OutgoingInternalTransition<>(x.getLetter(), getUnionState(x.getSucc(), true))));
		} else {
			mSecondAutomaton.getSuccessors(originalStateInformation.getSecond()).forEach(x -> result
					.add(new OutgoingInternalTransition<>(x.getLetter(), getUnionState(x.getSucc(), false))));
		}
		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {

		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();

		final Pair<Boolean, STATE> originalStateInformation = mAutomatonMap.get(state);

		if (Boolean.TRUE.equals(originalStateInformation.getFirst())) {
			mFirstAutomaton.getSuccessors(originalStateInformation.getSecond(), letter).forEach(
					x -> result.add(new OutgoingInternalTransition<>(letter, getUnionState(x.getSucc(), true))));
		} else {
			mFirstAutomaton.getSuccessors(originalStateInformation.getSecond(), letter).forEach(
					x -> result.add(new OutgoingInternalTransition<>(letter, getUnionState(x.getSucc(), false))));
		}
		return result;
	}

	/**
	 * this method creates different states, even if states in mFirstAutomaton and mSecondAutomaton have the same name,
	 * furthermore it checks if they are finite or accepting and adds them to the respective set. if a UnionState was
	 * already created this method returns its value without further computation
	 *
	 * @param originalState
	 *            a state from either of mFirstAutomaton or mSecondAutomaton
	 * @param isFirst
	 *            a boolean that declares explicitly if this state is from mFirstAutomaton or mSecondAutomaton
	 * @return
	 */
	private STATE getUnionState(final STATE originalState, final boolean isFirst) {
		final STATE newState;
		if (isFirst) {
			newState = mFactory.getBlackContent(originalState);
			if (mAutomatonMap.containsKey(newState)) {
				return newState;
			}

			if (mFirstAutomaton.isFinite(originalState)) {
				mFiniteStates.add(newState);
			}
			if (mFirstAutomaton.isAccepting(originalState)) {
				mAcceptingStates.add(newState);
			}
		} else {
			newState = mFactory.getWhiteContent(originalState);
			if (mAutomatonMap.containsKey(newState)) {
				return newState;
			}

			if (mSecondAutomaton.isFinite(originalState)) {
				mFiniteStates.add(newState);
			}
			if (mSecondAutomaton.isAccepting(originalState)) {
				mAcceptingStates.add(newState);
			}
		}
		mAutomatonMap.put(newState, new Pair<>(isFirst, originalState));

		return newState;
	}
}
