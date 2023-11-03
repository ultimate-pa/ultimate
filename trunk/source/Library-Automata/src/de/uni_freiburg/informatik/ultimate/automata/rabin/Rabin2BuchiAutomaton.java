/*
 * Copyright (C) 2023 Philipp Müller (pm251@venus.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
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
		return mNonFiniteSet.contains(state) && mRabinAutomaton.isAccepting(mBuchi2Rabin.get(state));
	}

	@Override
	public int size() {
		// Maybe compute this eager ?
		return mBuchi2Rabin.size();
	}

	@Override
	public String sizeInformation() {
		return "Number of distinct computed states so far: " + size();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		return getSucessors(state, mRabinAutomaton.getSuccessors(mBuchi2Rabin.get(state), letter));
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		return getSucessors(state, mRabinAutomaton.getSuccessors(mBuchi2Rabin.get(state)));
	}

	/**
	 * a helper method for internalSucessors
	 *
	 * @param buchiState
	 *            the state which is the root for all transitions in the Buchi automaton
	 * @param rabinTransitions
	 *            the transitions for the parent of this buchiState in the Rabin automaton which should be considered
	 * @return the derived transitions for the Buchi automaton
	 */
	private Iterable<OutgoingInternalTransition<LETTER, STATE>> getSucessors(final STATE buchiState,
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> rabinTransitions) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();
		// if the state is non-finite it can only have nonFinite successors
		if (mNonFiniteSet.contains(buchiState)) {
			for (final OutgoingInternalTransition<LETTER, STATE> transition : rabinTransitions) {
				final STATE succ = getNonFiniteVariant(transition.getSucc());
				if (succ != null) {
					result.add(new OutgoingInternalTransition<>(transition.getLetter(), succ));
				}
			}
			return result;
		}
		for (final OutgoingInternalTransition<LETTER, STATE> transition : rabinTransitions) {
			final STATE rabinSucc = transition.getSucc();
			result.add(new OutgoingInternalTransition<>(transition.getLetter(), getFiniteVariant(rabinSucc)));

			final STATE nonFiniteVariant = getNonFiniteVariant(rabinSucc);
			if (nonFiniteVariant != null) {
				// we only consider accepting states as entries into the non-finite subautomaton, this removes
				// cul-de-sac paths without accepting components from being computed without necessity
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
