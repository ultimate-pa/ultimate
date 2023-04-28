package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IConcurrentProductStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

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
public class RabinIntersection<LETTER, STATE, FACTORY extends IBlackWhiteStateFactory<STATE> & IConcurrentProductStateFactory<STATE>>
		implements IRabinAutomaton<LETTER, STATE> {
	private final IRabinAutomaton<LETTER, STATE> mFirstAutomaton;
	private final IRabinAutomaton<LETTER, STATE> mSecondAutomaton;
	private final FACTORY mFactory;

	private HashSet<LETTER> mAlphabet;
	private HashSet<STATE> mInitialStates;

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
	}

	@Override
	public Set<LETTER> getAlphabet() {
		if (mAlphabet == null) {
			mAlphabet = new HashSet<>();
			mAlphabet.addAll(mFirstAutomaton.getAlphabet());
			mAlphabet.retainAll(mSecondAutomaton.getAlphabet());
		}

		return mAlphabet;
	}

	@Override
	public int size() {
		return (mFirstAutomaton.size() * mSecondAutomaton.size()) * 4;
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
		if (mInitialStates == null) {
			mInitialStates = new HashSet<>();
			for (final STATE firstInitial : mFirstAutomaton.getInitialStates()) {
				for (final STATE secondInitial : mSecondAutomaton.getInitialStates()) {
					mInitialStates.add(getProducedState(firstInitial, secondInitial, 0));
				}
			}
		}

		return mInitialStates;
	}

	@Override
	public boolean isInitial(final STATE state) {

		return mInitialStates.contains(state);
	}

	@Override
	public boolean isAccepting(final STATE state) {

		return false;
	}

	@Override
	public boolean isFinite(final STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	private STATE getProducedState(final STATE first, final STATE second, final int subsetIndex) {
		STATE result = mFactory.concurrentProduct(first, second);

		// The four subautomata from the "Why These Automata Types?" - Udi Boker page 7 Theorem 1 are labeled in Binary
		// where White corresponds to 0 and Black to 1

		switch (subsetIndex) {
		case 0:
			result = mFactory.getWhiteContent(mFactory.getWhiteContent(result));
			break;
		case 1:
			result = mFactory.getWhiteContent(mFactory.getBlackContent(result));
			break;
		case 2:

			result = mFactory.getBlackContent(mFactory.getWhiteContent(result));
			break;
		case 3:
			result = mFactory.getBlackContent(mFactory.getBlackContent(result));
			break;
		default:
			return null;
		}

		return result;
	}

}
