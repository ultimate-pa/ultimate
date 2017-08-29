/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.SetOfStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quad;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quin;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;

/**
 * undocumented!
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NestedWordAutomatonCache<LETTER, STATE> implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	private static final String STATE = "State ";
	private static final String NOT_IN_AUTOMATON = " not in automaton";
	private static final String UNKNOWN = " unknown";

	protected final IEmptyStackStateFactory<STATE> mStateFactory;

	protected final AutomataLibraryServices mServices;
	protected final ILogger mLogger;

	private final VpAlphabet<LETTER> mVpAlphabet;

	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map PREs -> LETTERs -> SUCCs.
	 */
	protected final NestedMap3<STATE, LETTER, STATE, IsContained> mInternalOut = new NestedMap3<>();

	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map PREs -> LETTERs -> SUCCs.
	 */
	protected final NestedMap3<STATE, LETTER, STATE, IsContained> mCallOut = new NestedMap3<>();

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as map LinPREs -> LETTERs -> HierPREs ->
	 * SUCCs.
	 */
	protected final NestedMap4<STATE, STATE, LETTER, STATE, IsContained>  mReturnOut = new NestedMap4<>();

	protected final SetOfStates<STATE> mSetOfStates;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param internalAlphabet
	 *            internal alphabet
	 * @param callAlphabet
	 *            call alphabet
	 * @param returnAlphabet
	 *            return alphabet
	 * @param stateFactory
	 *            state factory
	 */
	public NestedWordAutomatonCache(final AutomataLibraryServices services, 
			final VpAlphabet<LETTER> vpAlphabet,
			final IEmptyStackStateFactory<STATE> stateFactory) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mVpAlphabet = vpAlphabet;
		if (stateFactory == null) {
			throw new IllegalArgumentException("nwa must have stateFactory");
		}
		mStateFactory = stateFactory;
		mSetOfStates = new SetOfStates<STATE>(mStateFactory.createEmptyStackState());
	}
	
	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mVpAlphabet;
	}

	public final Set<STATE> getStates() {
		return mSetOfStates.getStates();
	}
	
	public final Set<STATE> getFinalStates() {
		return mSetOfStates.getAcceptingStates();
	}

	@Override
	public final STATE getEmptyStackState() {
		return mSetOfStates.getEmptyStackState();
	}

	@Override
	public final IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	/**
	 * @param state
	 *            A state.
	 * @return {@code true} iff the automaton contains the state
	 */
	public final boolean contains(final STATE state) {
		return mSetOfStates.getStates().contains(state);
	}

	@Override
	public final int size() {
		return mSetOfStates.getStates().size();
	}

	@Override
	public final Set<STATE> getInitialStates() {
		return mSetOfStates.getInitialStates();
	}

	@Override
	public final boolean isInitial(final STATE state) {
		return mSetOfStates.isInitial(state);
	}

	@Override
	public final boolean isFinal(final STATE state) {
		return mSetOfStates.isAccepting(state);
	}

	/**
	 * @param isInitial
	 *            {@code true} iff state is initial.
	 * @param isFinal
	 *            {@code true} iff state is accepting
	 * @param state
	 *            state
	 */
	@SuppressWarnings("squid:S2301")
	public void addState(final boolean isInitial, final boolean isFinal, final STATE state) {
		mSetOfStates.addState(isInitial, isFinal, state);
	}

	@Override
	public final Set<LETTER> lettersInternal(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE + state + UNKNOWN);
		}
		final NestedMap2<LETTER, STATE, IsContained> map = mInternalOut.get(state);
		return map == null ? Collections.emptySet() : map.keySet();
	}

	@Override
	public final Set<LETTER> lettersCall(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE + state + UNKNOWN);
		}
		final NestedMap2<LETTER, STATE, IsContained> map = mCallOut.get(state);
		return map == null ? Collections.emptySet() : map.keySet();
	}

	public final Set<LETTER> lettersReturn(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE + state + UNKNOWN);
		}
		final NestedMap3<STATE, LETTER, STATE, IsContained> map = mReturnOut.get(state);
		if (map == null) {
			return Collections.emptySet();
		} else {
			final Set<LETTER> result = new HashSet<>();
			for (final Quad<STATE, LETTER, STATE, IsContained> entry : map.entrySet()) {
				result.add(entry.getSecond());
			}
			return result;
		}
	}
	
	@Override
	public final Set<LETTER> lettersReturn(final STATE state, final STATE hier) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE + state + UNKNOWN);
		}
		final NestedMap2<LETTER, STATE, IsContained> map = mReturnOut.get(state, hier);
		if (map == null) {
			return Collections.emptySet();
		} else {
			return map.keySet();
		}
	}

	/**
	 * @param state
	 *            A state.
	 * @return all respective hierarchical predecessors
	 */
	public final Collection<STATE> hierPred(final STATE state) {
		assert contains(state);
		final NestedMap3<STATE, LETTER, STATE, IsContained> map = mReturnOut.get(state);
		if (map == null) {
			return Collections.emptySet();
		} else {
			return map.keySet();
		}
	}

	/**
	 * @param state
	 *            A state.
	 * @param letter
	 *            internal letter
	 * @return all respective internal successors
	 */
	public final Set<STATE> succInternal(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<STATE, IsContained> map = mInternalOut.get(state, letter);
		if (map == null) {
			return null;
		}
		return map.keySet();
	}

	/**
	 * @param state
	 *            A state.
	 * @param letter
	 *            call letter
	 * @return all respective call successors
	 */
	public final Set<STATE> succCall(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<STATE, IsContained> map = mCallOut.get(state, letter);
		if (map == null) {
			return null;
		}
		return map.keySet();
	}

	/**
	 * @param state
	 *            A state.
	 * @param hier
	 *            hierarchical predecessor
	 * @param letter
	 *            return letter
	 * @return all respective return successors
	 */
	public final Set<STATE> succReturn(final STATE state, final STATE hier, final LETTER letter) {
		assert contains(state);
		assert contains(hier);
		final Map<STATE, IsContained> map = mReturnOut.get(state, hier, letter);
		if (map == null) {
			return null;
		}
		return map.keySet();
	}

	@Override
	public final Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		return NestedWordAutomataUtils.constructInternalTransitionIteratorFromNestedMap(state, letter, mInternalOut);
	}



	@Override
	public final Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		return () -> new TransformIterator<Quad<STATE, LETTER, STATE, IsContained>, OutgoingInternalTransition<LETTER, STATE>>(
				mInternalOut.entries(state).iterator(), x -> new OutgoingInternalTransition<LETTER, STATE>(x.getSecond(), x.getThird()));
	}

	@Override
	public final Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		return NestedWordAutomataUtils.constructCallTransitionIteratorFromNestedMap(state, letter, mCallOut);
	}



	@Override
	public final Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		return () -> new TransformIterator<Quad<STATE, LETTER, STATE, IsContained>, OutgoingCallTransition<LETTER, STATE>>(
				mCallOut.entries(state).iterator(), x -> new OutgoingCallTransition<LETTER, STATE>(x.getSecond(), x.getThird()));
	}

	@Override
	public final Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		return NestedWordAutomataUtils.constructReturnTransitionIteratorFromNestedMap(state, hier, letter, mReturnOut);
	}



	@Override
	public final Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		return () -> new TransformIterator<Quin<STATE, STATE, LETTER, STATE, IsContained>, OutgoingReturnTransition<LETTER, STATE>>(
				mReturnOut.entries(state, hier).iterator(), x -> new OutgoingReturnTransition<LETTER, STATE>(x.getSecond(), x.getThird(), x.getFourth()));
	}

	/**
	 * @param state
	 *            The predecessor state.
	 * @param letter
	 *            internal letter
	 * @param succ
	 *            successor state
	 * @return {@code true} iff automaton contains respective transition
	 */
	public final boolean containsInternalTransition(final STATE state, final LETTER letter, final STATE succ) {
		assert contains(state);
		return mInternalOut.get(state, letter, succ) != null;
	}

	/**
	 * @param state
	 *            The predecessor state.
	 * @param letter
	 *            call letter
	 * @param succ
	 *            successor state
	 * @return {@code true} iff automaton contains respective transition
	 */
	public final boolean containsCallTransition(final STATE state, final LETTER letter, final STATE succ) {
		assert contains(state);
		return mCallOut.get(state, letter, succ) != null;
	}

	/**
	 * @param state
	 *            The predecessor state.
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            return letter
	 * @param succ
	 *            successor state
	 * @return {@code true} iff automaton contains respective transition
	 */
	public final boolean containsReturnTransition(final STATE state, final STATE hier, final LETTER letter,
			final STATE succ) {
		assert contains(state);
		assert contains(hier);
		return mReturnOut.get(state, hier, letter, succ) != null;
	}

	@Override
	public String sizeInformation() {
		final boolean verbose = false;
		if (!verbose) {
			final int states = getStates().size();
			return states + " states.";
		}
		final int statesWithInternalSuccessors;
		final Set<STATE> statesWithOutgoingInternal = mInternalOut.keySet();
		if (statesWithOutgoingInternal == null) {
			statesWithInternalSuccessors = 0;
		} else {
			statesWithInternalSuccessors = statesWithOutgoingInternal.size();
		}
		final int internalSuccessors = mInternalOut.size();
		
		final int statesWithCallSuccessors;
		final Set<STATE> statesWithOutgoingCall = mCallOut.keySet();
		if (statesWithOutgoingCall == null) {
			statesWithCallSuccessors = 0;
		} else {
			statesWithCallSuccessors = statesWithOutgoingCall.size();
		}
		final int callSuccessors = mCallOut.size();

		int statesWithReturnSuccessor;
		final Set<STATE> statesWithOutgoingReturn = mReturnOut.keySet();
		if (statesWithOutgoingReturn == null) {
			statesWithReturnSuccessor = 0;
		} else {
			statesWithReturnSuccessor = statesWithOutgoingReturn.size();
		}
		final int returnSuccessors = mReturnOut.size();

		final StringBuilder sb = new StringBuilder();
		sb.append(" has ").append(getStates().size()).append(" states, " + statesWithInternalSuccessors)
				.append(" states have internal successors, (").append(internalSuccessors).append("), ")
				.append(statesWithCallSuccessors).append(" states have call successors, (").append(callSuccessors)
				.append("), ").append(statesWithReturnSuccessor).append(" states have return successors, (")
				.append(returnSuccessors).append("), ");
		return sb.toString();
	}

	private boolean assertThatAllStatesAreInAutomaton(final Collection<STATE> succs) {
		boolean result = true;
		for (final STATE state : succs) {
			result &= contains(state);
			assert result : STATE + state + NOT_IN_AUTOMATON;
		}
		return result;
	}

	/**
	 * @param pred
	 *            The predecessor state.
	 * @param letter
	 *            internal letter
	 * @param succ
	 *            successor state
	 */
	public void addInternalTransition(final STATE pred, final LETTER letter, final STATE succ) {
		if (!contains(pred)) {
			throw new IllegalArgumentException(STATE + pred + NOT_IN_AUTOMATON);
		}
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert contains(succ) : STATE + succ + NOT_IN_AUTOMATON;
		assert getVpAlphabet().getInternalAlphabet().contains(letter);
		mInternalOut.put(pred, letter, succ, IsContained.IsContained);
	}

	/**
	 * @param pred
	 *            The predecessor state.
	 * @param letter
	 *            internal letter
	 * @param succs
	 *            successor states
	 */
	public void addInternalTransitions(final STATE pred, final LETTER letter, final Collection<STATE> succs) {
		if (!getVpAlphabet().getInternalAlphabet().contains(letter)) {
			throw new IllegalArgumentException("letter" + letter + " not in internal alphabet");
		}
		if (!contains(pred)) {
			throw new IllegalArgumentException(STATE + pred + NOT_IN_AUTOMATON);
		}
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert assertThatAllStatesAreInAutomaton(succs);
		assert getVpAlphabet().getInternalAlphabet().contains(letter);
		for (final STATE succ : succs) {
			addInternalTransition(pred, letter, succ);
		}
	}

	/**
	 * @param pred
	 *            The predecessor state.
	 * @param letter
	 *            call letter
	 * @param succ
	 *            successor state
	 */
	public void addCallTransition(final STATE pred, final LETTER letter, final STATE succ) {
		if (!getVpAlphabet().getCallAlphabet().contains(letter)) {
			throw new IllegalArgumentException("letter" + letter + " not in call alphabet");
		}
		
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert contains(succ) : STATE + succ + NOT_IN_AUTOMATON;
		assert getVpAlphabet().getCallAlphabet().contains(letter);
		mCallOut.put(pred, letter, succ, IsContained.IsContained);
	}

	/**
	 * @param pred
	 *            The predecessor state.
	 * @param letter
	 *            call letter
	 * @param succs
	 *            successor states
	 */
	public void addCallTransitions(final STATE pred, final LETTER letter, final Collection<STATE> succs) {
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert assertThatAllStatesAreInAutomaton(succs);
		assert getVpAlphabet().getCallAlphabet().contains(letter);
		for (final STATE succ : succs) {
			addCallTransition(pred, letter, succ);
		}
	}

	/**
	 * @param pred
	 *            The linear predecessor state.
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            return letter
	 * @param succ
	 *            successor state
	 */
	public void addReturnTransition(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		if (!getVpAlphabet().getReturnAlphabet().contains(letter)) {
			throw new IllegalArgumentException("letter" + letter + " not in return alphabet");
		}
		
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert contains(succ) : STATE + succ + NOT_IN_AUTOMATON;
		assert contains(hier) : STATE + hier + NOT_IN_AUTOMATON;
		assert getVpAlphabet().getReturnAlphabet().contains(letter);
		mReturnOut.put(pred, hier, letter, succ, IsContained.IsContained);
	}

	/**
	 * @param pred
	 *            The linear predecessor state.
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            return letter
	 * @param succs
	 *            successor states
	 */
	public void addReturnTransitions(final STATE pred, final STATE hier, final LETTER letter,
			final Collection<STATE> succs) {
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert assertThatAllStatesAreInAutomaton(succs);
		assert contains(hier) : STATE + hier + NOT_IN_AUTOMATON;
		assert getVpAlphabet().getReturnAlphabet().contains(letter);
		for (final STATE succ : succs) {
			addReturnTransition(pred, hier, letter, succ);
		}
	}
	
	
	protected final void removeInternalOut(final STATE pred, final LETTER letter, final STATE succ) {
		mInternalOut.remove(pred, letter, succ);
	}
	
	protected final void removeAllInternalOut(final STATE pred) {
		mInternalOut.remove(pred);
	}
	
	protected final void removeCallOut(final STATE pred, final LETTER letter, final STATE succ) {
		mCallOut.remove(pred, letter, succ);
	}
	
	protected final void removeAllCallOut(final STATE pred) {
		mCallOut.remove(pred);
	}
	
	protected final void removeReturnOut(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		mReturnOut.remove(pred, hier, letter, succ);
	}
	
	protected final void removeAllReturnOut(final STATE pred) {
		mReturnOut.remove(pred);
	}

	/**
	 * @return {@code true} iff this automaton is deterministic.
	 */
	public final boolean isDeterministic() {
		if (getInitialStates().size() > 1) {
			return false;
		}
		for (final STATE state : this.getStates()) {
			if (!isDeterministic(state)) {
				return false;
			}
		}
		return true;
	}

	private boolean isDeterministic(final STATE state) {
		for (final LETTER symbol : lettersInternal(state)) {
			if (succInternal(state, symbol).size() > 1) {
				return false;
			}
		}
		for (final LETTER symbol : lettersCall(state)) {
			if (succCall(state, symbol).size() > 1) {
				return false;
			}
		}
		for (final STATE hier : hierPred(state)) {
			for (final LETTER symbol : lettersReturn(state, hier)) {
				if (succReturn(state, hier, symbol).size() > 1) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * @return {@code true} iff this automaton is total.
	 */
	public final boolean isTotal() {
		if (getInitialStates().isEmpty()) {
			return false;
		}
		for (final STATE state : this.getStates()) {
			if (!isTotal(state)) {
				return false;
			}
		}
		return true;
	}

	private boolean isTotal(final STATE state) {
		for (final LETTER symbol : getVpAlphabet().getInternalAlphabet()) {
			if (succInternal(state, symbol).isEmpty()) {
				return false;
			}
		}
		for (final LETTER symbol : getVpAlphabet().getCallAlphabet()) {
			if (succCall(state, symbol).isEmpty()) {
				return false;
			}
		}
		for (final LETTER symbol : getVpAlphabet().getReturnAlphabet()) {
			for (final STATE hier : getStates()) {
				if (succReturn(state, hier, symbol).isEmpty()) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * @param state
	 *            A state.
	 * @return number of outgoing internal transitions
	 */
	public final int numberOfOutgoingInternalTransitions(final STATE state) {
		int result = 0;
		for (final LETTER letter : lettersInternal(state)) {
			result += succInternal(state, letter).size();
		}
		return result;
	}

	@Override
	public String toString() {
		return (new AutomatonDefinitionPrinter<String, String>(mServices, "nwa", Format.ATS, this))
				.getDefinitionAsString();
	}
	
	public int computeNumberOfInternalTransitions() {
		return mInternalOut.size();
	}
}
