/**
 *
 */
package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

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
	private final IBlackWhiteStateFactory<STATE> mFiniteOrNonFiniteStateFactory;
	private final HashMap<STATE, STATE> mBuchi2Rabin = new HashMap<>();

	private final HashSet<STATE> mInitialSet = new HashSet<>();
	private boolean mInitialComplete;
	private final HashSet<STATE> mNonFiniteSet = new HashSet<>();
	private final HashSet<STATE> mAcceptingSet = new HashSet<>();

	/**
	 *
	 */
	public Rabin2BuchiAutomaton(final IRabinAutomaton<LETTER, STATE> automaton,
			final IBlackWhiteStateFactory<STATE> finiteOrNonFiniteStateFactory) {
		mRabinAutomaton = automaton;
		mFiniteOrNonFiniteStateFactory = finiteOrNonFiniteStateFactory;
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return new VpAlphabet<>(mRabinAutomaton.getAlphabet());
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		if (!mInitialComplete) {

			if (mRabinAutomaton.getInitialStates().spliterator().estimateSize() != (2 * mInitialSet.size())) {

				mRabinAutomaton.getInitialStates().forEach(x -> {
					final Iterator<STATE> relatedStates = explore(x).iterator();

					mInitialSet.add(relatedStates.next());
					if (relatedStates.hasNext()) {
						mInitialSet.add(relatedStates.next());
					}
				});
			}
			mInitialComplete = true;
		}
		return mInitialSet;
	}

	@Override
	public boolean isInitial(final STATE state) {
		if (mInitialSet.contains(state)) {
			return true;
		}
		if (mBuchi2Rabin.containsKey(state)) {

			if (mRabinAutomaton.isInitial(mBuchi2Rabin.get(state))) {
				mInitialSet.add(state);
				return true;
			}
			return false;
		}

		// exception if state not known
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

		if (mAcceptingSet.contains(state)) {
			return true;
		}
		if (mBuchi2Rabin.containsKey(state)) {
			return false;
		}
		// exception if state not known
	}

	@Override
	public int size() {
		// Maybe compute this eager
		return mBuchi2Rabin.size();
	}

	@Override
	public String sizeInformation() {
		return "Number of cached states: " + size();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();
		final STATE rabinState = mBuchi2Rabin.get(state);
		if (mNonFiniteSet.contains(state)) {
			mRabinAutomaton.getSuccessors(rabinState, letter).forEach(x -> {
				final STATE succ = exploreFromNonFinite(x.getSucc());
				if (succ != null) {
					result.add(new OutgoingInternalTransition<>(letter, succ));
				}
			});

			return result;
		}
		if (mBuchi2Rabin.containsKey(state)) {
			mRabinAutomaton.getSuccessors(rabinState, letter).forEach(x -> {
				final Iterator<STATE> successors = explore(x.getSucc()).iterator();
				result.add(new OutgoingInternalTransition<>(letter, successors.next()));
				if (successors.hasNext()) {
					result.add(new OutgoingInternalTransition<>(letter, successors.next()));
				}
			});

			return result;
		}

		return null;
	}

	@SuppressWarnings("deprecation")
	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mFiniteOrNonFiniteStateFactory;
	}

	private ArrayList<STATE> explore(final STATE rabinState) {

		final STATE finiteVariant = mFiniteOrNonFiniteStateFactory.getWhiteContent(rabinState);
		final STATE nonFiniteVariant = mFiniteOrNonFiniteStateFactory.getBlackContent(rabinState);

		final ArrayList<STATE> result = new ArrayList<>(2);
		result.add(finiteVariant);

		if (mBuchi2Rabin.containsKey(finiteVariant)) {
			if (mBuchi2Rabin.containsKey(nonFiniteVariant)) {
				result.add(nonFiniteVariant);
			}
			return result;
		}

		mBuchi2Rabin.put(finiteVariant, rabinState);

		if (!mRabinAutomaton.isFinite(rabinState)) {
			mBuchi2Rabin.put(nonFiniteVariant, rabinState);
			mNonFiniteSet.add(nonFiniteVariant);
			result.add(nonFiniteVariant);

			if (mRabinAutomaton.isAccepting(rabinState)) {
				mAcceptingSet.add(nonFiniteVariant);
			}
		}
		return result;
	}

	private STATE exploreFromNonFinite(final STATE rabinState) {

		final STATE nonFiniteVariant = mFiniteOrNonFiniteStateFactory.getBlackContent(rabinState);

		if (mBuchi2Rabin.containsKey(nonFiniteVariant)) {

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
		return null;
	}

	@Override
	public STATE getEmptyStackState() {
		// There is no stack in Rabin automata
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		// There are no call Transitions in Rabin automata
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		// There are no return Transitions in Rabin automata
		return null;
	}

}
