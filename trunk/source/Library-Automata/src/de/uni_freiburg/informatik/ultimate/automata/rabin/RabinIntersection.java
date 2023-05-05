package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IConcurrentProductStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * A class that lazyly constructs the intersection production from Udi Boker: “Why these automata types?,” in LPAR-22.
 * 22nd International Conference on Logic for Programming, Artificial Intelligence and Reasoning, Awassa, Ethiopia,
 * 16-21 November 2018 (G. Barthe, G. Sutcliffe, and M. Veanes, eds.), vol. 57 of EPiC Series in Computing, pp. 143–163,
 * EasyChair, 2018. !The construction is found page 7, Theorem 1!
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letter
 * @param <STATE>
 *            type of state
 * @param <FACTORY>
 *            a factory that can return the product of two state{@link IConcurrentProductStateFactory} and label states
 *            binaray ({@link IBlackWhiteStateFactory}
 */
public class RabinIntersection<LETTER, STATE, FACTORY extends IRainbowStateFactory<STATE> & IIntersectionStateFactory<STATE>>
		implements IRabinAutomaton<LETTER, STATE> {
	private final IRabinAutomaton<LETTER, STATE> mFirstAutomaton;
	private final IRabinAutomaton<LETTER, STATE> mSecondAutomaton;
	private final FACTORY mFactory;

	private final HashSet<STATE> mInitialStates = new HashSet<>();
	private final HashSet<STATE> mFiniteStates = new HashSet<>();
	private final HashSet<STATE> mAcceptingStates = new HashSet<>();
	private final HashMap<STATE, Triple<STATE, STATE, mComponent>> mAutomatonMap = new HashMap<>();

	// This references the components from the Boker construction and maps them to colors for IRainbowStateFactory
	private enum mComponent {
		ZERO(1), ONE(2), TWO(3), THREE(4);

		private byte mColor;

		mComponent(final int i) {
			mColor = (byte) i;
		}
	}

	/**
	 * implementation that lazyly constructs the intersection of two Rabin automata
	 *
	 * @param firstAutomaton
	 *            first Rabin automaton to intersect
	 * @param secondAutomaton
	 *            second Rabin automaton to intersect
	 * @param factory
	 *            some (BlackWhiteStateFactory & ConcurrentProductStateFactory) for STATE
	 */
	public RabinIntersection(final IRabinAutomaton<LETTER, STATE> firstAutomaton,
			final IRabinAutomaton<LETTER, STATE> secondAutomaton, final FACTORY factory) {
		mFirstAutomaton = firstAutomaton;
		mSecondAutomaton = secondAutomaton;
		mFactory = factory;

		for (final STATE firstInitial : mFirstAutomaton.getInitialStates()) {
			for (final STATE secondInitial : mSecondAutomaton.getInitialStates()) {
				mInitialStates.add(getProducedState(firstInitial, secondInitial, mComponent.ZERO));
			}
		}
	}

	@Override
	public Set<LETTER> getAlphabet() {
		assert mFirstAutomaton.getAlphabet().equals(mSecondAutomaton.getAlphabet());

		return mFirstAutomaton.getAlphabet();
	}

	@Override
	public int size() {
		return (mFirstAutomaton.size() * mSecondAutomaton.size()) * mComponent.values().length;
	}

	@Override
	public String sizeInformation() {

		return "Number of states: " + size() + "\n"
				+ "The number of lazyly constructed reachable states may be smaller";
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

		final Triple<STATE, STATE, mComponent> originalStateInformation = mAutomatonMap.get(state);
		final STATE originalFirstState = originalStateInformation.getFirst();
		final STATE originalSecondState = originalStateInformation.getSecond();
		final mComponent originalComponent = originalStateInformation.getThird();

		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result =
				getProductSuccessor(originalFirstState, originalSecondState,
						mComponent.values()[((originalComponent.ordinal() + 1) % mComponent.values().length)]);

		if (originalComponent.equals(mComponent.ZERO) || originalComponent.equals(mComponent.TWO)) {

			result.addAll(getProductSuccessor(originalFirstState, originalSecondState, originalComponent));
		}

		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {

		final Triple<STATE, STATE, mComponent> originalStateInformation = mAutomatonMap.get(state);
		final STATE originalFirstState = originalStateInformation.getFirst();
		final STATE originalSecondState = originalStateInformation.getSecond();
		final mComponent originalComponent = originalStateInformation.getThird();

		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result =
				getProductSuccessor(originalFirstState, originalSecondState,
						mComponent.values()[((originalComponent.ordinal() + 1) % mComponent.values().length)], letter);

		if (originalComponent.equals(mComponent.ZERO) || originalComponent.equals(mComponent.TWO)) {

			result.addAll(getProductSuccessor(originalFirstState, originalSecondState, originalComponent, letter));
		}

		return result;
	}

	/**
	 * Constructs product states for different subautomata used in this product construction
	 *
	 * @param first
	 *            state from mFirstAutomaton
	 * @param second
	 *            state from mSecondAutomaton
	 * @param component
	 *            a component referencing the subautomaton
	 * @return a state which uniquely incorporates all parameters
	 */
	private STATE getProducedState(final STATE first, final STATE second, final mComponent component) {

		STATE result = mFactory.intersection(first, second);
		result = mFactory.getColoredState(result, component.mColor);
		if (!mAutomatonMap.containsKey(result)) {
			if (component.equals(mComponent.ONE) && mFirstAutomaton.isAccepting(first)) {
				mAcceptingStates.add(result);
			}

			// With the used construction Finite states are either in B' or B"
			// Check if in B'
			boolean isBad = mFirstAutomaton.isFinite(first) || mSecondAutomaton.isFinite(second);
			// if false, check if in B"
			isBad = isBad || (component.equals(mComponent.ONE) && !mFirstAutomaton.isAccepting(first));
			isBad = isBad || (component.equals(mComponent.THREE) && !mSecondAutomaton.isAccepting(second));
			if (isBad) {
				mFiniteStates.add(result);
			}

			mAutomatonMap.put(result, new Triple<>(first, second, component));
		}

		return result;
	}

	private ArrayList<OutgoingInternalTransition<LETTER, STATE>> getProductSuccessor(final STATE first,
			final STATE second, final mComponent successorComponent) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();

		for (final OutgoingInternalTransition<LETTER, STATE> transitionFirst : mFirstAutomaton.getSuccessors(first)) {
			final LETTER letter = transitionFirst.getLetter();
			for (final OutgoingInternalTransition<LETTER, STATE> transitionSecond : mSecondAutomaton
					.getSuccessors(second, letter)) {
				result.add(new OutgoingInternalTransition<>(letter,
						getProducedState(transitionFirst.getSucc(), transitionSecond.getSucc(), successorComponent)));
			}
		}

		return result;
	}

	private ArrayList<OutgoingInternalTransition<LETTER, STATE>> getProductSuccessor(final STATE first,
			final STATE second, final mComponent successorComponent, final LETTER letter) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();

		for (final OutgoingInternalTransition<LETTER, STATE> transitionFirst : mFirstAutomaton.getSuccessors(first,
				letter)) {
			for (final OutgoingInternalTransition<LETTER, STATE> transitionSecond : mSecondAutomaton
					.getSuccessors(second, letter)) {
				result.add(new OutgoingInternalTransition<>(letter,
						getProducedState(transitionFirst.getSucc(), transitionSecond.getSucc(), successorComponent)));
			}
		}

		return result;
	}
}
