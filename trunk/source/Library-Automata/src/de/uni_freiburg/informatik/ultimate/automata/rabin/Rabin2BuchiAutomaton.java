/**
 *
 */
package de.uni_freiburg.informatik.ultimate.automata.rabin;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * lazy translation of a Rabin automaton into an equivalent Büchi automaton
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 */
public class Rabin2BuchiAutomaton<LETTER, STATE> implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {

	private final IRabinAutomaton<LETTER, STATE> mRabinAutomaton;
	// black states ~ accepting, white states ~ NonAccepting
	private final IBlackWhiteStateFactory<STATE> mAcceptingOrNonAcceptingStateFactory;

	/**
	 *
	 */
	public Rabin2BuchiAutomaton(final IRabinAutomaton<LETTER, STATE> automaton,
			final IBlackWhiteStateFactory<STATE> acceptingOrNonAcceptingStateFactory) {
		mRabinAutomaton = automaton;
		mAcceptingOrNonAcceptingStateFactory = acceptingOrNonAcceptingStateFactory;
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return new VpAlphabet<>(mRabinAutomaton.getAlphabet());
	}

	/**
	 * There is no stack in Rabin automata
	 */
	@Override
	public STATE getEmptyStackState() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		// TODO: generate Iterable with usage of mAcceptingOrNonAcceptingStateFactory on
		// mRabinAutomaton.getInitialStates()
		return null;

	}

	@Override
	public boolean isInitial(final STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFinal(final STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@SuppressWarnings("deprecation")
	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mAcceptingOrNonAcceptingStateFactory;
	}

}
