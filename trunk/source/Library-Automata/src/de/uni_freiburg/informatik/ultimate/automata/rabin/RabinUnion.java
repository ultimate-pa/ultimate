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

	IRabinAutomaton<LETTER, STATE> mFirstAutomaton;
	IRabinAutomaton<LETTER, STATE> mSecondAutomaton;
	IBlackWhiteStateFactory<STATE> mFactory;
	HashSet<LETTER> mAlphabet;
	HashSet<STATE> mInitialStates;
	HashSet<STATE> mFiniteStates;
	HashSet<STATE> mAcceptingStates;
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
	}

	@Override
	public Set<LETTER> getAlphabet() {
		if (mAlphabet == null) {
			mAlphabet = new HashSet<>();
			mAlphabet.addAll(mFirstAutomaton.getAlphabet());
			mAlphabet.addAll(mSecondAutomaton.getAlphabet());
		}
		return mAlphabet;
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
		if (mInitialStates == null) {
			final HashSet<STATE> result = new HashSet<>();
			mFirstAutomaton.getInitialStates().forEach(x -> {
				final STATE firstState = mFactory.getBlackContent(x);
				result.add(firstState);
				mAutomatonMap.put(firstState, new Pair<>(true, x));
			});
			mSecondAutomaton.getInitialStates().forEach(x -> {
				final STATE secondState = mFactory.getWhiteContent(x);
				result.add(secondState);
				mAutomatonMap.put(secondState, new Pair<>(false, x));
			});
			mInitialStates = result;

		}
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
			mFirstAutomaton.getSuccessors(originalStateInformation.getSecond()).forEach(x -> {
				final STATE originalSucc = x.getSucc();
				final STATE newSucc = mFactory.getBlackContent(originalSucc);

				mAutomatonMap.putIfAbsent(newSucc, new Pair<>(true, originalSucc));
				result.add(new OutgoingInternalTransition<>(x.getLetter(), newSucc));

			});
		} else {
			mSecondAutomaton.getSuccessors(originalStateInformation.getSecond()).forEach(x -> {
				final STATE originalSucc = x.getSucc();
				final STATE newSucc = mFactory.getWhiteContent(originalSucc);

				mAutomatonMap.putIfAbsent(newSucc, new Pair<>(false, originalSucc));
				result.add(new OutgoingInternalTransition<>(x.getLetter(), newSucc));

			});
		}
		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {

		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();

		final Pair<Boolean, STATE> originalStateInformation = mAutomatonMap.get(state);

		if (Boolean.TRUE.equals(originalStateInformation.getFirst())) {
			mFirstAutomaton.getSuccessors(originalStateInformation.getSecond(), letter).forEach(x -> {
				final STATE originalSucc = x.getSucc();
				final STATE newSucc = mFactory.getBlackContent(originalSucc);

				mAutomatonMap.putIfAbsent(newSucc, new Pair<>(true, originalSucc));
				result.add(new OutgoingInternalTransition<>(x.getLetter(), newSucc));

			});
		} else {
			mSecondAutomaton.getSuccessors(originalStateInformation.getSecond(), letter).forEach(x -> {
				final STATE originalSucc = x.getSucc();
				final STATE newSucc = mFactory.getWhiteContent(originalSucc);

				mAutomatonMap.putIfAbsent(newSucc, new Pair<>(false, originalSucc));
				result.add(new OutgoingInternalTransition<>(x.getLetter(), newSucc));

			});
		}
		return result;
	}

}
