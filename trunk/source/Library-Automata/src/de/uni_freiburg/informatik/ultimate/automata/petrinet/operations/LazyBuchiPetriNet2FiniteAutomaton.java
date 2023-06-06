/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022-2023 Daniel Küchler (kuechlerdaniel33@gmail.com)
 * Copyright (C) 2020-2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaCacheBookkeeping;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * On-the-fly construction of a finite Automaton from a Petri Net.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters in the Petri net
 * @param <S>
 *            The type of places in the Petri net, and also the type of states in the resulting finite automaton.
 */
// TODO: This class is just a slight modification of LazyPetriNet2FiniteAutomaton.
// To reduce duplicate code we should use an abstract class for the common code.
public class LazyBuchiPetriNet2FiniteAutomaton<L, S> implements INwaOutgoingLetterAndTransitionProvider<L, S> {

	private final IPetriNetTransitionProvider<L, S> mOperand;
	private final Predicate<Marking<S>> mIsKnownDeadEnd;
	private final IPetriNet2FiniteAutomatonStateFactory<S> mStateFactory;

	private final IBlackWhiteStateFactory<S> mAcceptingOrNonAcceptingStateFactory;

	private final Map<Marking<S>, S> mMarking2AcceptingState = new HashMap<>();
	private final Map<Marking<S>, S> mMarking2NonAcceptingState = new HashMap<>();

	// Needed to compute outgoing transitions. If all outgoing transitions of a state have been computed, we remove the
	// state from this map (to save on memory).
	private final Map<S, Marking<S>> mState2Marking = new HashMap<>();

	private final NwaCacheBookkeeping<L, S> mCacheBookkeeping = new NwaCacheBookkeeping<>();
	private final NestedWordAutomatonCache<L, S> mCache;

	/**
	 * Creates a new instance for a given net.
	 *
	 * @param services
	 *            Automata library services object
	 * @param factory
	 *            state factory used to create automaton states
	 * @param operand
	 *            Petri Net that is converted to a finite automaton
	 * @param isKnownDeadEnd
	 *            Function that can identify (some) dead end states. Dead end states will be omitted from constructed
	 *            automaton. Set to null if not needed.
	 *
	 * @throws PetriNetNot1SafeException
	 *             Petri Net has to be one-safe
	 */
	public LazyBuchiPetriNet2FiniteAutomaton(final AutomataLibraryServices services,
			final IPetriNet2FiniteAutomatonStateFactory<S> factory,
			final IBlackWhiteStateFactory<S> acceptingNonacceptingFactory,
			final IPetriNetTransitionProvider<L, S> operand, final Predicate<Marking<S>> isKnownDeadEnd)
			throws PetriNetNot1SafeException {
		mOperand = operand;
		mIsKnownDeadEnd = isKnownDeadEnd;
		mStateFactory = factory;
		mAcceptingOrNonAcceptingStateFactory = acceptingNonacceptingFactory;
		mCache = new NestedWordAutomatonCache<>(services, new VpAlphabet<>(mOperand.getAlphabet()), factory);

		// construct the initial state
		constructState(new Marking<>(ImmutableSet.of(mOperand.getInitialPlaces())), true, false);
	}

	@Deprecated
	@Override
	public IStateFactory<S> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mCache.getVpAlphabet();
	}

	@Override
	public S getEmptyStackState() {
		return mCache.getEmptyStackState();
	}

	@Override
	public Iterable<S> getInitialStates() {
		return mCache.getInitialStates();
	}

	@Override
	public boolean isInitial(final S state) {
		return mCache.isInitial(state);
	}

	@Override
	public boolean isFinal(final S state) {
		return mCache.isFinal(state);
	}

	@Override
	public int size() {
		return mMarking2AcceptingState.size() + mMarking2NonAcceptingState.size();
	}

	@Override
	public String sizeInformation() {
		return "currently " + size() + " states, but on-demand construction may add more states";
	}

	@Override
	public Set<L> lettersInternal(final S state) {
		final Marking<S> marking = mState2Marking.get(state);
		if (marking == null) {
			// All outgoing transitions already cached.
			return mCache.lettersInternal(state);
		}
		return getOutgoingNetTransitions(marking).map(Transition::getSymbol).collect(Collectors.toSet());
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		if (!mCacheBookkeeping.isCachedInternal(state, letter)) {
			computeOutgoingTransitions(state, letter);

			// Check if now all transitions have been cached. If so, we no longer need the marking.
			if (mCacheBookkeeping.countCachedInternal(state) == lettersInternal(state).size()) {
				mState2Marking.remove(state);
			}
		}
		return mCache.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state) {
		// Check if there might be uncached transitions, and if so, compute and cache them.
		if (mState2Marking.containsKey(state)) {
			for (final L letter : lettersInternal(state)) {
				if (!mCacheBookkeeping.isCachedInternal(state, letter)) {
					computeOutgoingTransitions(state, letter);
				}
			}
			// Now all transitions have been cached. We no longer need the marking.
			mState2Marking.remove(state);
		}

		return mCache.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<L, S>> callSuccessors(final S state, final L letter) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, S>> returnSuccessors(final S state, final S hier, final L letter) {
		return Collections.emptySet();
	}

	private void computeOutgoingTransitions(final S state, final L letter) {
		final Marking<S> marking = mState2Marking.get(state);
		if (marking == null) {
			// All outgoing transitions already cached.
			return;
		}
		getOutgoingNetTransitions(marking).filter(t -> t.getSymbol().equals(letter)).distinct()
				.forEach(t -> createAutomatonTransition(state, marking, t));
	}

	private void createAutomatonTransition(final S state, final Marking<S> marking, final Transition<L, S> transition) {
		try {
			final boolean firesIntoAcceptingPlace = transition.getSuccessors().stream().anyMatch(mOperand::isAccepting);
			final S successor = getOrConstructState(marking.fireTransition(transition), firesIntoAcceptingPlace);
			if (successor != null) {
				mCache.addInternalTransition(state, transition.getSymbol(), successor);
			}
			mCacheBookkeeping.reportCachedInternal(state, transition.getSymbol());
		} catch (final PetriNetNot1SafeException e) {
			throw new IllegalArgumentException("Petri net must be 1-safe!", e);
		}
	}

	private S getOrConstructState(final Marking<S> marking, final boolean isAccepting) {
		// Do not use computeIfAbsent, because constructState may return null.
		if (isAccepting) {
			if (!mMarking2AcceptingState.containsKey(marking)) {
				final S state = constructState(marking, false, isAccepting);
				mMarking2AcceptingState.put(marking, state);
				return state;
			}
			return mMarking2AcceptingState.get(marking);
		}
		if (!mMarking2NonAcceptingState.containsKey(marking)) {
			final S state = constructState(marking, false, isAccepting);
			mMarking2NonAcceptingState.put(marking, state);
			return state;
		}
		return mMarking2NonAcceptingState.get(marking);
	}

	private S constructState(final Marking<S> marking, final boolean isInitial, final boolean isAccepting) {
		if (isKnownDeadEnd(marking)) {
			return null;
		}

		S state = mStateFactory.getContentOnPetriNet2FiniteAutomaton(marking);

		if (isAccepting) {
			state = mAcceptingOrNonAcceptingStateFactory.getWhiteContent(state);
		} else {
			state = mAcceptingOrNonAcceptingStateFactory.getBlackContent(state);
		}

		mState2Marking.put(state, marking);

		assert isInitial == new Marking<>(ImmutableSet.of(mOperand.getInitialPlaces()))
				.equals(marking) : "Wrong initial state";
		mCache.addState(isInitial, isAccepting, state);

		return state;
	}

	private Stream<Transition<L, S>> getOutgoingNetTransitions(final Marking<S> marking) {
		return marking.stream().flatMap(place -> mOperand.getSuccessors(place).stream())
				.filter(marking::isTransitionEnabled);
	}

	private boolean isKnownDeadEnd(final Marking<S> marking) {
		if (mIsKnownDeadEnd == null) {
			return false;
		}
		return mIsKnownDeadEnd.test(marking);
	}
}
