/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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

import java.util.Arrays;
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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

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
public class LazyPetriNet2FiniteAutomaton<L, S> implements INwaOutgoingLetterAndTransitionProvider<L, S> {

	private final IPetriNet<L, S> mOperand;
	private final Predicate<S> mIsKnownDeadEnd;
	private final IPetriNet2FiniteAutomatonStateFactory<S> mStateFactory;
	private final Map<Marking<L, S>, S> mMarking2State = new HashMap<>();
	private final Map<S, Marking<L, S>> mState2Marking = new HashMap<>();

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
	 *             Petri Net has to be 1Safe
	 */
	public LazyPetriNet2FiniteAutomaton(final AutomataLibraryServices services,
			final IPetriNet2FiniteAutomatonStateFactory<S> factory, final IPetriNet<L, S> operand,
			final Predicate<S> isKnownDeadEnd) throws PetriNetNot1SafeException {
		mOperand = operand;
		mIsKnownDeadEnd = isKnownDeadEnd;
		mStateFactory = factory;
		mCache = new NestedWordAutomatonCache<>(services, new VpAlphabet<>(mOperand.getAlphabet()), factory);
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
		return Arrays.asList(getOrConstructState(new Marking<>(mOperand.getInitialPlaces())));
	}

	private S getOrConstructState(final Marking<L, S> marking) {
		return mMarking2State.computeIfAbsent(marking, x -> {
			final S state = mStateFactory.getContentOnPetriNet2FiniteAutomaton(marking);
			mState2Marking.put(state, marking);

			final boolean isInitial = new Marking<>(mOperand.getInitialPlaces()).equals(marking);
			final boolean isFinal = mOperand.isAccepting(marking);
			mCache.addState(isInitial, isFinal, state);

			return state;
		});
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
		return mMarking2State.size();
	}

	@Override
	public String sizeInformation() {
		return "currently " + size() + " states, but on-demand construction may add more states";
	}

	@Override
	public Set<L> lettersInternal(final S state) {
		if (isKnownDeadEnd(state)) {
			return Collections.emptySet();
		}
		return getOutgoingNetTransitions(mState2Marking.get(state)).map(ITransition::getSymbol)
				.collect(Collectors.toSet());
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		if (isKnownDeadEnd(state)) {
			return Collections.emptySet();
		}
		if (!mCacheBookkeeping.isCachedInternal(state, letter)) {
			computeOutgoingTransitions(state, letter);
		}
		return mCache.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state) {
		for (final L letter : lettersInternal(state)) {
			if (!mCacheBookkeeping.isCachedInternal(state, letter)) {
				computeOutgoingTransitions(state, letter);
			}
		}
		return mCache.internalSuccessors(state);
	}

	private void computeOutgoingTransitions(final S state, final L letter) {
		final Marking<L, S> marking = mState2Marking.get(state);
		getOutgoingNetTransitions(marking).filter(t -> t.getSymbol().equals(letter)).distinct()
				.forEach(t -> createAutomatonTransition(state, marking, t));
	}

	private void createAutomatonTransition(final S state, final Marking<L, S> marking,
			final ITransition<L, S> transition) {
		try {
			final Marking<L, S> succMarking = marking.fireTransition(transition, mOperand);
			final S succState = getOrConstructState(succMarking);
			if (!isKnownDeadEnd(succState)) {
				mCache.addInternalTransition(state, transition.getSymbol(), succState);
				mCacheBookkeeping.reportCachedInternal(state, transition.getSymbol());
			}
		} catch (final PetriNetNot1SafeException e) {
			throw new IllegalArgumentException("Petri net must be 1-safe!", e);
		}
	}

	private Stream<ITransition<L, S>> getOutgoingNetTransitions(final Marking<L, S> marking) {
		return marking.stream().flatMap(place -> mOperand.getSuccessors(place).stream())
				.filter(t -> marking.isTransitionEnabled(t, mOperand));
	}

	@Override
	public Iterable<OutgoingCallTransition<L, S>> callSuccessors(final S state, final L letter) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, S>> returnSuccessors(final S state, final S hier, final L letter) {
		return Collections.emptySet();
	}

	private boolean isKnownDeadEnd(final S state) {
		if (mIsKnownDeadEnd == null) {
			return false;
		}
		return mIsKnownDeadEnd.test(state);
	}
}
