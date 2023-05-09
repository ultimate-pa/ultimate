/**
 *
 */
package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * lazy translation of a Rabin automaton into an equivalent Büchi automaton. Do not use Rabin States for operations on
 * this automaton!
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @param <FACTORY>
 *            state factory with IBlackWhiteState & IEmptyStackState functionality
 *
 */
public class Rabin2BuchiAutomaton<LETTER, STATE, FACTORY extends IBlackWhiteStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
		implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {

	private final IRabinAutomaton<LETTER, STATE> mRabinAutomaton;
	// black states ~ nonFinite, white states ~ Finite
	private final FACTORY mFiniteOrNonFiniteStateFactory;
	// references for a reversal of the BlackWhite modification
	private final HashMap<STATE, STATE> mBuchi2Rabin = new HashMap<>();

	private final HashSet<STATE> mInitialSet = new HashSet<>();
	private final HashSet<STATE> mNonFiniteSet = new HashSet<>();
	private final HashSet<STATE> mAcceptingSet = new HashSet<>();

	/**
	 * Initializes lazy Buchi conversion for a Rabin automaton using the given BWStateFactory
	 *
	 * @param automaton
	 *            the Rabin automaton to be converted
	 * @param finiteOrNonFiniteStateFactory
	 *            a factory mapping a set of states to two non intersecting sets of states
	 */
	public Rabin2BuchiAutomaton(final IRabinAutomaton<LETTER, STATE> automaton,
			final FACTORY finiteOrNonFiniteStateFactory) {
		mRabinAutomaton = automaton;
		mFiniteOrNonFiniteStateFactory = finiteOrNonFiniteStateFactory;

		for (final STATE init : automaton.getInitialStates()) {
			mInitialSet.add(getFiniteVariant(init));
			final STATE nonFiniteCandidate = getNonFiniteVariant(init);
			if (nonFiniteCandidate != null) {
				mInitialSet.add(nonFiniteCandidate);
			}
		}
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return new VpAlphabet<>(mRabinAutomaton.getAlphabet());
	}

	@Override
	public Iterable<STATE> getInitialStates() {

		return mInitialSet;
	}

	@Override
	public boolean isInitial(final STATE state) {

		return mInitialSet.contains(state);
	}

	/**
	 * Computes if a state is accepting (Final means accepting in this context) only returns a boolean iff the state is
	 * reached through lazy construction
	 *
	 * @param state
	 *            state which acceptance should be evaluated
	 * @return
	 */
	@Override
	public boolean isFinal(final STATE state) {

		return mAcceptingSet.contains(state);
	}

	@Override
	public int size() {
		// Maybe compute this eager ?
		return mBuchi2Rabin.size();
	}

	@Override
	public String sizeInformation() {
		return "Number of distinct computed states: " + size();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {

		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();

		final STATE rabinState = mBuchi2Rabin.get(state);
		if (mNonFiniteSet.contains(state)) {

			for (final OutgoingInternalTransition<LETTER, STATE> transition : mRabinAutomaton.getSuccessors(rabinState,
					letter)) {

				final STATE succ = getNonFiniteVariant(transition.getSucc());
				if (succ != null) {
					result.add(new OutgoingInternalTransition<>(letter, succ));
				}
			}

			return result;
		}

		for (final OutgoingInternalTransition<LETTER, STATE> transition : mRabinAutomaton.getSuccessors(rabinState,
				letter)) {
			final STATE rabinSucc = transition.getSucc();
			result.add(new OutgoingInternalTransition<>(letter, getFiniteVariant(rabinSucc)));
			final STATE nonFiniteVariant = getNonFiniteVariant(rabinSucc);

			if (nonFiniteVariant != null) {
				if (isFinal(nonFiniteVariant)) {
					result.add(new OutgoingInternalTransition<>(letter, nonFiniteVariant));
				}
			}
		}

		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {

		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();

		final STATE rabinState = mBuchi2Rabin.get(state);
		if (mNonFiniteSet.contains(state)) {
			for (final OutgoingInternalTransition<LETTER, STATE> transition : mRabinAutomaton
					.getSuccessors(rabinState)) {
				final STATE succ = getNonFiniteVariant(transition.getSucc());
				if (succ != null) {
					result.add(new OutgoingInternalTransition<>(transition.getLetter(), succ));
				}
			}

			return result;
		}

		for (final OutgoingInternalTransition<LETTER, STATE> transition : mRabinAutomaton.getSuccessors(rabinState)) {
			final STATE rabinSucc = transition.getSucc();
			result.add(new OutgoingInternalTransition<>(transition.getLetter(), getFiniteVariant(rabinSucc)));
			final STATE nonFiniteVariant = getNonFiniteVariant(rabinSucc);

			if (nonFiniteVariant != null) {
				if (isFinal(nonFiniteVariant)) {
					result.add(new OutgoingInternalTransition<>(transition.getLetter(), nonFiniteVariant));
				}
			}
		}
		return result;
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mFiniteOrNonFiniteStateFactory;
	}

	/**
	 * creates a finite variant of a state if not already created and returns this variant
	 *
	 * @param rabinState
	 *            a state from the original Rabin automaton
	 * @return the finite variant in the here computed Buchi automaton
	 */
	private STATE getFiniteVariant(final STATE rabinState) {

		final STATE finiteVariant = mFiniteOrNonFiniteStateFactory.getWhiteContent(rabinState);

		if (mBuchi2Rabin.containsKey(finiteVariant)) {

			return finiteVariant;
		}
		mBuchi2Rabin.put(finiteVariant, rabinState);

		return finiteVariant;
	}

	/**
	 * creates a nonFinite variant of a state if not already created and returns this variant
	 *
	 * @param rabinState
	 *            a state from the original Rabin automaton
	 * @return the nonFinite variant in the here computed Buchi automaton
	 */
	private STATE getNonFiniteVariant(final STATE rabinState) {

		final STATE nonFiniteVariant = mFiniteOrNonFiniteStateFactory.getBlackContent(rabinState);

		if (mNonFiniteSet.contains(nonFiniteVariant)) {

			return nonFiniteVariant;
		}

		if (!mRabinAutomaton.isFinite(rabinState)) {
			mBuchi2Rabin.put(nonFiniteVariant, rabinState);
			mNonFiniteSet.add(nonFiniteVariant);

			if (mRabinAutomaton.isAccepting(rabinState)) {
				mAcceptingSet.add(nonFiniteVariant);
			}
			return nonFiniteVariant;
		}
		// A Finite state can never produce a nonFinite Buchi variant
		return null;
	}

	@Override
	public STATE getEmptyStackState() {
		// There is no stack in Rabin automata
		return mFiniteOrNonFiniteStateFactory.createEmptyStackState();
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		// There are no call Transitions in Rabin automata
		return Set.of();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		// There are no return Transitions in Rabin automata
		return Set.of();
	}
}
