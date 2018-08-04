/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ConcurrentProduct;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IConcurrentProductStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedIteratorNoopConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quin;

/**
 * Standard implementation of the #{@link de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton}
 * interface.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NestedWordAutomaton<LETTER, STATE> extends NestedWordAutomatonCache<LETTER, STATE> implements INestedWordAutomaton<LETTER, STATE>  {
	private static final String LETTER2 = "Letter ";
	private static final String NOT_IN_AUTOMATON = " not in automaton";
	private static final String STATE2 = "State ";
	private static final String UNKNOWN = " unknown";


	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map SUCCs -> LETTERs -> PREs.
	 */
	private final Map<STATE, Map<LETTER, Set<STATE>>> mInternalIn = new HashMap<>();

	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map SUCCs -> LETTERs -> PREs.
	 */
	private final Map<STATE, Map<LETTER, Set<STATE>>> mCallIn = new HashMap<>();

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as map HierPREs -> LETTERs -> LinPREs ->
	 * SUCCs.
	 */
	private final Map<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> mReturnSummary = new HashMap<>();

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as map SUCCs -> LETTERs -> HierPREs ->
	 * LinPREs.
	 */
	private final Map<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> mReturnIn = new HashMap<>();

	public NestedWordAutomaton(final AutomataLibraryServices services, final VpAlphabet<LETTER> vpAlphabet,
			final IEmptyStackStateFactory<STATE> emptyStateFactory) {
		super(services, vpAlphabet, emptyStateFactory);
	}


	@Override
	public Set<LETTER> lettersInternalIncoming(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE2 + state + UNKNOWN);
		}
		final Map<LETTER, Set<STATE>> map = mInternalIn.get(state);
		return map == null ? Collections.emptySet() : map.keySet();
	}

	@Override
	public Set<LETTER> lettersCallIncoming(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE2 + state + UNKNOWN);
		}
		final Map<LETTER, Set<STATE>> map = mCallIn.get(state);
		return map == null ? Collections.emptySet() : map.keySet();
	}

	@Override
	public Set<LETTER> lettersReturnIncoming(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE2 + state + UNKNOWN);
		}
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnIn.get(state);
		return map == null ? Collections.emptySet() : map.keySet();
	}

	@Override
	public Set<LETTER> lettersSummary(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE2 + state + UNKNOWN);
		}
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnSummary.get(state);
		return map == null ? Collections.emptySet() : map.keySet();
	}

	private Set<STATE> predInternal(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mInternalIn.get(state);
		if (map == null) {
			return Collections.emptySet();
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? Collections.emptySet() : result;
	}

	private Set<STATE> predCall(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mCallIn.get(state);
		if (map == null) {
			return Collections.emptySet();
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? Collections.emptySet() : result;
	}

	public Set<STATE> hierarchicalPredecessorsOutgoing(final STATE state) {
		assert contains(state);
		final NestedMap3<STATE, LETTER, STATE, IsContained> tmp = mReturnOut.get(state);
		if (tmp == null) {
			return Collections.emptySet();
		} else {
			return tmp.keySet();
		}
	}

	@Override
	public Set<STATE> hierarchicalPredecessorsOutgoing(final STATE state, final LETTER letter) {
		assert contains(state);
		final Set<STATE> result = new HashSet<>();
		for (final Quin<STATE, STATE, LETTER, STATE, IsContained> entry : mReturnOut.entries(state)) {
			if (entry.getThird().equals(letter)) {
				result.add(entry.getSecond());
			}
		}
		return result;
	}

	private Set<STATE> predReturnLin(final STATE state, final LETTER letter, final STATE hier) {
		assert contains(state);
		assert contains(hier);
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = mReturnIn.get(state);
		if (letter2hier2preds == null) {
			return Collections.emptySet();
		}
		final Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		if (hier2preds == null) {
			return Collections.emptySet();
		}
		final Set<STATE> result = hier2preds.get(hier);
		return result == null ? Collections.emptySet() : result;
	}

	private Set<STATE> predReturnHier(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = mReturnIn.get(state);
		if (letter2hier2preds == null) {
			return Collections.emptySet();
		}
		final Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		if (hier2preds == null) {
			return Collections.emptySet();
		}
		return hier2preds.keySet();
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier, final LETTER letter) {
		final Set<SummaryReturnTransition<LETTER, STATE>> result = new HashSet<>();
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = mReturnSummary.get(hier);
		if (letter2pred2succs == null) {
			return result;
		}
		final Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
		if (pred2succs == null) {
			return result;
		}
		for (final Entry<STATE, Set<STATE>> entry : pred2succs.entrySet()) {
			final STATE pred = entry.getKey();
			final Set<STATE> succs = entry.getValue();
			if (succs != null) {
				for (final STATE succ : succs) {
					final SummaryReturnTransition<LETTER, STATE> srt =
							new SummaryReturnTransition<>(pred, letter, succ);
					result.add(srt);
				}
			}
		}
		return result;
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier) {
		return () -> new NestedIteratorNoopConstruction<LETTER, SummaryReturnTransition<LETTER, STATE>>(
				lettersSummary(hier).iterator(), x -> summarySuccessors(hier, x).iterator());
	}


	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ,
			final LETTER letter) {
		return () -> new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
			private final Iterator<STATE> mIterator = initialize();

			private Iterator<STATE> initialize() {
				final Map<LETTER, Set<STATE>> letter2pred = mInternalIn.get(succ);
				if (letter2pred != null && letter2pred.get(letter) != null) {
					return letter2pred.get(letter).iterator();
				}
				return null;
			}

			@Override
			public boolean hasNext() {
				return mIterator != null && mIterator.hasNext();
			}

			@Override
			public IncomingInternalTransition<LETTER, STATE> next() {
				if (mIterator == null) {
					throw new NoSuchElementException();
				}
				final STATE pred = mIterator.next();
				return new IncomingInternalTransition<>(pred, letter);
			}
		};
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ) {
		return () -> new NestedIteratorNoopConstruction<LETTER, IncomingInternalTransition<LETTER, STATE>>(
				lettersInternalIncoming(succ).iterator(), x -> internalPredecessors(succ, x).iterator());
	}


	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ, final LETTER letter) {
		return () -> new Iterator<IncomingCallTransition<LETTER, STATE>>() {
			private final Iterator<STATE> mIterator = initialize();

			private Iterator<STATE> initialize() {
				final Map<LETTER, Set<STATE>> letter2pred = mCallIn.get(succ);
				if (letter2pred != null && letter2pred.get(letter) != null) {
					return letter2pred.get(letter).iterator();
				}
				return null;
			}

			@Override
			public boolean hasNext() {
				return mIterator != null && mIterator.hasNext();
			}

			@Override
			public IncomingCallTransition<LETTER, STATE> next() {
				if (mIterator == null) {
					throw new NoSuchElementException();
				}
				final STATE pred = mIterator.next();
				return new IncomingCallTransition<>(pred, letter);
			}
		};
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ) {
		return () -> new NestedIteratorNoopConstruction<LETTER, IncomingCallTransition<LETTER, STATE>>(
				lettersCallIncoming(succ).iterator(), x -> callPredecessors(succ, x).iterator());
	}


	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final STATE hier,
			final LETTER letter) {
		return () -> new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
			private final Iterator<STATE> mIterator = initialize();

			private Iterator<STATE> initialize() {
				final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = mReturnIn.get(succ);
				if (letter2hier2pred != null) {
					final Map<STATE, Set<STATE>> hier2pred = letter2hier2pred.get(letter);
					if (hier2pred != null && hier2pred.get(hier) != null) {
						return hier2pred.get(hier).iterator();
					}
				}
				return null;
			}

			@Override
			public boolean hasNext() {
				return mIterator != null && mIterator.hasNext();
			}

			@Override
			public IncomingReturnTransition<LETTER, STATE> next() {
				if (mIterator == null) {
					throw new NoSuchElementException();
				}
				final STATE pred = mIterator.next();
				return new IncomingReturnTransition<>(pred, hier, letter);
			}
		};
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final LETTER letter) {
		return () -> new NestedIteratorNoopConstruction<STATE, IncomingReturnTransition<LETTER, STATE>>(
				predReturnHier(succ, letter).iterator(), x -> returnPredecessors(succ, x, letter).iterator());
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ) {
		return () -> new NestedIteratorNoopConstruction<LETTER, IncomingReturnTransition<LETTER, STATE>>(
				lettersReturnIncoming(succ).iterator(), x -> returnPredecessors(succ, x).iterator());
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final LETTER letter) {
		return () -> new NestedIteratorNoopConstruction<STATE, OutgoingReturnTransition<LETTER, STATE>>(
				hierarchicalPredecessorsOutgoing(state, letter).iterator(), x -> returnSuccessors(state, x, letter).iterator());
	}


	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state) {
		return () -> new NestedIteratorNoopConstruction<STATE, OutgoingReturnTransition<LETTER, STATE>>(
				hierarchicalPredecessorsOutgoing(state).iterator(), x -> returnSuccessorsGivenHier(state, x).iterator());
	}


	private boolean checkTransitionsReturnedConsistent() {
		boolean result = true;
		for (final STATE state : getStates()) {
			for (final IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(state)) {
				result &= containsInternalTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
				result &= containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
			}
			for (final IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(state)) {
				result &= containsCallTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
			}
			for (final OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state)) {
				result &= containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
			}
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(state)) {
				result &= containsReturnTransition(inTrans.getLinPred(), inTrans.getHierPred(), inTrans.getLetter(),
						state);
				assert result;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state)) {
				result &= containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(),
						outTrans.getSucc());
				assert result;
			}
		}

		return result;
	}

	/**
	 * @param state
	 *            A state which is made non-initial.
	 * @deprecated
	 * 			Do not modify existing automata, construct new automata instead.
	 */
	@Deprecated
	public void makeStateNonIntial(final STATE state) {
		mSetOfStates.makeStateNonInitial(state);
	}

	/**
	 * @param state
	 *            A state which is removed.
	 */
	public void removeState(final STATE state) {

		for (final OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state)) {
			removeCallIn(state, outTrans.getLetter(), outTrans.getSucc());
		}
		removeAllCallOut(state);

		for (final LETTER letter : lettersCallIncoming(state)) {
			for (final STATE pred : predCall(state, letter)) {
				removeCallOut(pred, letter, state);
			}
		}
		mCallIn.remove(state);

		for (final OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state)) {
			removeReturnIn(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
			removeReturnSummary(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());

		}
		removeAllReturnOut(state);

		final Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = mReturnSummary.get(state);
		if (letter2pred2succs != null) {
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry1 : letter2pred2succs.entrySet()) {
				final LETTER letter = entry1.getKey();
				final Map<STATE, Set<STATE>> pred2succs = entry1.getValue();
				if (pred2succs != null) {
					for (final Entry<STATE, Set<STATE>> entry2 : pred2succs.entrySet()) {
						final STATE pred = entry2.getKey();
						final Set<STATE> succs = entry2.getValue();
						if (succs != null) {
							for (final STATE succ : succs) {
								removeReturnIn(pred, state, letter, succ);
								removeReturnOut(pred, state, letter, succ);
							}
						}
					}
				}
			}
		}
		mReturnSummary.remove(state);

		for (final LETTER letter : lettersReturnIncoming(state)) {
			final Map<STATE, Set<STATE>> hier2pred = mReturnIn.get(state).get(letter);
			for (final STATE hier : hier2pred.keySet()) {
				for (final STATE pred : predReturnLin(state, letter, hier)) {
					removeReturnOut(pred, hier, letter, state);
					removeReturnSummary(pred, hier, letter, state);
				}
			}
		}
		mReturnIn.remove(state);

		for (final LETTER letter : lettersInternalIncoming(state)) {
			for (final STATE pred : predInternal(state, letter)) {
				removeInternalOut(pred, letter, state);
			}
		}
		mInternalIn.remove(state);

		for (final OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
			removeInternalIn(state, outTrans.getLetter(), outTrans.getSucc());
		}
		removeAllInternalOut(state);

		mSetOfStates.removeState(state);

		// assert checkTransitionsStoredConsistent();
		assert checkTransitionsReturnedConsistent();
		assert sizeInformation().length() > 0;
	}

	private void removeInternalIn(final STATE pred, final LETTER letter, final STATE succ) {
		final Map<LETTER, Set<STATE>> letter2preds = mInternalIn.get(succ);
		final Set<STATE> preds = letter2preds.get(letter);
		assert preds.contains(pred);
		preds.remove(pred);
		if (preds.isEmpty()) {
			letter2preds.remove(letter);
			if (letter2preds.isEmpty()) {
				mInternalIn.remove(succ);
			}
		}
	}



	private void removeCallIn(final STATE pred, final LETTER letter, final STATE succ) {
		final Map<LETTER, Set<STATE>> letter2preds = mCallIn.get(succ);
		final Set<STATE> preds = letter2preds.get(letter);
		assert preds.contains(pred);
		preds.remove(pred);
		if (preds.isEmpty()) {
			letter2preds.remove(letter);
			if (letter2preds.isEmpty()) {
				mCallIn.remove(succ);
			}
		}
	}



	private void removeReturnIn(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = mReturnIn.get(succ);
		final Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		final Set<STATE> preds = hier2preds.get(hier);
		assert preds.contains(pred);
		preds.remove(pred);
		if (preds.isEmpty()) {
			hier2preds.remove(hier);
			if (hier2preds.isEmpty()) {
				letter2hier2preds.remove(letter);
				if (letter2hier2preds.isEmpty()) {
					mReturnIn.remove(succ);
				}
			}
		}
	}



	private void removeReturnSummary(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = mReturnSummary.get(hier);
		final Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
		final Set<STATE> succs = pred2succs.get(pred);
		assert succs.contains(succ);
		succs.remove(succ);
		if (succs.isEmpty()) {
			pred2succs.remove(pred);
			if (pred2succs.isEmpty()) {
				letter2pred2succs.remove(letter);
				if (letter2pred2succs.isEmpty()) {
					mReturnSummary.remove(hier);
				}
			}
		}
	}

	private int numberIncomingInternalTransitions(final STATE state) {
		return numberOfElementsInIterable(internalPredecessors(state));
	}

	private int numberIncomingCallTransitions(final STATE state) {
		return numberOfElementsInIterable(callPredecessors(state));
	}

	private int numberIncomingReturnTransitions(final STATE state) {
		return numberOfElementsInIterable(returnPredecessors(state));
	}

	@SuppressWarnings("squid:S1481")
	private static int numberOfElementsInIterable(final Iterable<?> iterable) {
		int result = 0;
		for (final @SuppressWarnings("unused") Object obj : iterable) {
			result++;
		}
		return result;
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
		int statesWithInternalPredecessors = 0;
		int internalPredecessors = 0;
		for (final Entry<STATE, Map<LETTER, Set<STATE>>> entry1 : mInternalIn.entrySet()) {
			final Map<LETTER, Set<STATE>> letter2preds = entry1.getValue();
			int internalPredOfSucc = 0;
			statesWithInternalPredecessors++;
			for (final Entry<LETTER, Set<STATE>> entry2 : letter2preds.entrySet()) {
				final Set<STATE> preds = entry2.getValue();
				internalPredOfSucc += preds.size();
			}
			assert internalPredOfSucc == numberIncomingInternalTransitions(entry1.getKey());
			internalPredecessors += internalPredOfSucc;
		}

		final int statesWithCallSuccessors;
		final Set<STATE> statesWithOutgoingCall = mCallOut.keySet();
		if (statesWithOutgoingCall == null) {
			statesWithCallSuccessors = 0;
		} else {
			statesWithCallSuccessors = statesWithOutgoingCall.size();
		}

		final int callSuccessors = mCallOut.size();
		int statesWithCallPredecessors = 0;
		int callPredecessors = 0;
		for (final Entry<STATE, Map<LETTER, Set<STATE>>> entry1 : mCallIn.entrySet()) {
			statesWithCallPredecessors++;
			int callPredOfSucc = 0;
			final Map<LETTER, Set<STATE>> letter2preds = entry1.getValue();
			for (final Entry<LETTER, Set<STATE>> entry2 : letter2preds.entrySet()) {
				final Set<STATE> preds = entry2.getValue();
				callPredOfSucc += preds.size();
			}
			assert callPredOfSucc == numberIncomingCallTransitions(entry1.getKey());
			callPredecessors += callPredOfSucc;

		}

		int statesWithReturnSuccessor;
		final Set<STATE> statesWithOutgoingReturn = mReturnOut.keySet();
		if (statesWithOutgoingReturn == null) {
			statesWithReturnSuccessor = 0;
		} else {
			statesWithReturnSuccessor = statesWithOutgoingReturn.size();
		}
		final int returnSuccessors = mReturnOut.size();

		int statesWithReturnLinearPredecessors = 0;
		int returnLinearPredecessors = 0;
		for (final Entry<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> entry1 : mReturnIn.entrySet()) {
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = entry1.getValue();
			statesWithReturnLinearPredecessors++;
			int returnLinPredOfSucc = 0;
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry2 : letter2hier2pred.entrySet()) {
				final Map<STATE, Set<STATE>> hier2preds = entry2.getValue();
				for (final Entry<STATE, Set<STATE>> entry3 : hier2preds.entrySet()) {
					final Set<STATE> preds = entry3.getValue();
					returnLinPredOfSucc += preds.size();
				}
			}
			assert returnLinPredOfSucc == numberIncomingReturnTransitions(entry1.getKey());
			returnLinearPredecessors += returnLinPredOfSucc;
		}
		int statesWithReturnHierarchicalSuccessor = 0;
		int returnHierarchicalSuccessors = 0;
		for (final Entry<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> entry1 : mReturnSummary.entrySet()) {
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = entry1.getValue();
			statesWithReturnHierarchicalSuccessor++;
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry2 : letter2pred2succs.entrySet()) {
				final Map<STATE, Set<STATE>> pred2succs = entry2.getValue();
				for (final Entry<STATE, Set<STATE>> entry3 : pred2succs.entrySet()) {
					final Set<STATE> succs = entry3.getValue();
					returnHierarchicalSuccessors += succs.size();
				}
			}
		}
		final StringBuilder sb = new StringBuilder();
		sb.append(" has ").append(getStates().size()).append(" states, " + statesWithInternalSuccessors)
				.append(" states have internal successors, (").append(internalSuccessors).append("), ")
				.append(statesWithInternalPredecessors).append(" states have internal predecessors, (")
				.append(internalPredecessors).append("), ").append(statesWithCallSuccessors)

				.append(" states have call successors, (").append(callSuccessors).append("), ")
				.append(statesWithCallPredecessors).append(" states have call predecessors, (").append(callPredecessors)
				.append("), ").append(statesWithReturnSuccessor)

				.append(" states have return successors, (").append(returnSuccessors).append("), ")
				.append(statesWithReturnLinearPredecessors).append(" states have call predecessors, (")
				.append(returnLinearPredecessors).append("), " + statesWithReturnHierarchicalSuccessor)
				.append(" states have call successors, (").append(returnHierarchicalSuccessors).append(")");
		return sb.toString();

		/*
		return " has " + mInternalOut.size() + " states, " +
				statesWithInternalSuccessors + " states have internal successors, ("
				+ internalSuccessors + "), " +
				statesWithInternalPredecessors +
				" states have internal predecessors, (" + internalPredecessors +
				"), " +

				statesWithCallSuccessors + " states have call successors, (" +
				callSuccessors + "), " +
				statesWithCallPredecessors + " states have call predecessors, (" +
				callPredecessors + "), " +

				statesWithReturnSuccessor + " states have return successors, (" +
				returnSuccessors + "), " +
				statesWithReturnLinearPredecessors +
				" states have call predecessors, (" + returnLinearPredecessors +
				"), " +
				statesWithReturnHierarchicalSuccessor +
				" states have call successors, (" + returnHierarchicalSuccessors +
				")";
		*/
	}

	/**
	 * @param pred
	 *            The predecessor state.
	 * @param letter
	 *            internal letter
	 * @param succ
	 *            successor state
	 */
	@Override
	public void addInternalTransition(final STATE pred, final LETTER letter, final STATE succ) {
		super.addInternalTransition(pred, letter, succ);

		Map<LETTER, Set<STATE>> letter2preds = mInternalIn.get(succ);
		if (letter2preds == null) {
			letter2preds = new HashMap<>();
			mInternalIn.put(succ, letter2preds);
		}
		Set<STATE> preds = letter2preds.get(letter);
		if (preds == null) {
			preds = new HashSet<>();
			letter2preds.put(letter, preds);
		}
		preds.add(pred);
		// assert checkTransitionsStoredConsistent();
	}

	/**
	 * @param pred
	 *            The predecessor state.
	 * @param letter
	 *            call letter
	 * @param succ
	 *            successor state
	 */
	@Override
	public void addCallTransition(final STATE pred, final LETTER letter, final STATE succ) {
		super.addCallTransition(pred, letter, succ);

		Map<LETTER, Set<STATE>> letter2preds = mCallIn.get(succ);
		if (letter2preds == null) {
			letter2preds = new HashMap<>();
			mCallIn.put(succ, letter2preds);
		}
		Set<STATE> preds = letter2preds.get(letter);
		if (preds == null) {
			preds = new HashSet<>();
			letter2preds.put(letter, preds);
		}
		preds.add(pred);
		// assert checkTransitionsStoredConsistent();
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
	@Override
	public void addReturnTransition(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		super.addReturnTransition(pred, hier, letter, succ);

		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = mReturnIn.get(succ);
		if (letter2hier2preds == null) {
			letter2hier2preds = new HashMap<>();
			mReturnIn.put(succ, letter2hier2preds);
		}
		Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		if (hier2preds == null) {
			hier2preds = new HashMap<>();
			letter2hier2preds.put(letter, hier2preds);
		}
		Set<STATE> preds = hier2preds.get(hier);
		if (preds == null) {
			preds = new HashSet<>();
			hier2preds.put(hier, preds);
		}
		preds.add(pred);

		Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = mReturnSummary.get(hier);
		if (letter2pred2succs == null) {
			letter2pred2succs = new HashMap<>();
			mReturnSummary.put(hier, letter2pred2succs);
		}
		Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
		if (pred2succs == null) {
			pred2succs = new HashMap<>();
			letter2pred2succs.put(letter, pred2succs);
		}
		Set<STATE> succS = pred2succs.get(pred);
		if (succS == null) {
			succS = new HashSet<>();
			pred2succs.put(pred, succS);
		}
		succS.add(succ);
		// assert checkTransitionsStoredConsistent();
	}

	/*
	@Deprecated
	public NestedWordAutomaton(INestedWordAutomaton<LETTER,STATE> nwa,
			boolean totalize,
			boolean complement) {
		if (totalize && nwa.isTotal()) {
			throw new IllegalArgumentException(
					"Automaton is already total");
		}
		if (totalize && !nwa.isDeterministic()) {
			throw new IllegalArgumentException(
					"I only totalize deterministic NWAs");
		}
		if (complement && !(totalize || nwa.isTotal()) ) {
			throw new IllegalArgumentException(
					"I only complement total NWAs");
		}
		mInternalAlphabet = new HashSet<LETTER>();
		mInternalAlphabet.addAll(nwa.getInternalAlphabet());
		mCallAlphabet = new HashSet<LETTER>();
		mCallAlphabet.addAll(nwa.getCallAlphabet());
		mReturnAlphabet = new HashSet<LETTER>();
		mReturnAlphabet.addAll(nwa.getReturnAlphabet());
		mcontentFactory = nwa.getStateFactory();

		states = new HashSet<IAuxiliaryStateContainer<LETTER,STATE>>();
		initialStates = new
				HashSet<IAuxiliaryStateContainer<LETTER,STATE>>();
		finalStates = new HashSet<IAuxiliaryStateContainer<LETTER,STATE>>();

		emptyStackContent = mcontentFactory.createEmptyStackContent();
		emptyStackState = new AuxiliaryStateContainer<LETTER,STATE>(false,
				emptyStackContent, mConstructedStates++);
		assert(isFinalStoredConsistent((NestedWordAutomaton<LETTER, STATE>)
				nwa));



		for (STATE state : nwa.states()) {
			boolean isInitial = nwa.getInitial().contains(state);
			boolean isFinal;
			if (complement) {
				isFinal = !nwa.isFinal(state);
			}
			else {
				isFinal = nwa.isFinal(state);
			}
			addContent(isInitial, isFinal, state);
		}
		STATE sink = mcontentFactory.createSinkStateContent();
		//don't add sink state if automaton is already total
		if (totalize) {
			// sinkState is initial if automaton does not have initial states
			boolean isInitial = initialStates.isEmpty();
			addContent(isInitial, complement, sink);
		}

		for (STATE state : states()) {

			for (LETTER symbol : getInternalAlphabet()) {
				if (state == sink) {
					addInternalTransition(state, symbol, sink);
				}
				else {
					Collection<STATE> succs = nwa.succInternal(state, symbol);
					assert (!totalize || succs.size() <= 1);
					for (STATE succ : succs) {
						addInternalTransition(state, symbol, succ);
					}
					if (totalize && succs.isEmpty()) {
						addInternalTransition(state, symbol, sink);
					}
				}
			}

			for (LETTER symbol : getCallAlphabet()) {
				if (state == sink) {
					addCallTransition(state, symbol, sink);
				}
				else {
					Collection<STATE> succs = nwa.succCall(state, symbol);
					assert (!totalize || succs.size() <= 1);
					for (STATE succ : succs) {
						addCallTransition(state, symbol, succ);
					}
					if (totalize && succs.isEmpty()) {
						addCallTransition(state, symbol, sink);
					}
				}
			}

			for (LETTER symbol : getReturnAlphabet()) {
				for (STATE hier : states()) {
					if (state == sink) {
						addReturnTransition(state, hier, symbol, sink);
					}
					else if (hier == sink) {
						addReturnTransition(state, hier, symbol, sink);
					}
					else {
						Collection<STATE> succs = nwa.succReturn(state, hier, symbol);
						assert (!totalize || succs.size() <= 1);
						for (STATE succ : succs) {
							addReturnTransition(state, hier, symbol, succ);
						}
						if (totalize && succs.isEmpty()) {
							addReturnTransition(state, hier, symbol, sink);
						}
					}
				}
			}
		}
	}
	*/

	/**
	 * @return An accepting nested run.
	 * @throws AutomataOperationCanceledException
	 *             if operation is canceled
	 * @deprecated do not use this anymore
	 */
	@Deprecated
	public NestedRun<LETTER, STATE> getAcceptingNestedRun() throws AutomataOperationCanceledException {
		return (new IsEmpty<>(mServices, this)).getNestedRun();
	}


	/**
	 * @param nwa
	 *            A nested word automaton.
	 * @return nested word automaton which represents the concurrent product
	 */
	public INestedWordAutomaton<LETTER, STATE> concurrentProduct(final INestedWordAutomaton<LETTER, STATE> nwa) {
		// TODO Christian 2017-02-15 Temporary workaround, state factory should become a parameter
		//      Actually, this method should be removed!
		return (new ConcurrentProduct<>(mServices, (IConcurrentProductStateFactory<STATE>) mStateFactory, this, nwa,
				false)).getResult();
	}

	/**
	 * @param nwa
	 *            A nested word automaton.
	 * @return nested word automaton which represents the concurrent product prefix
	 */
	public INestedWordAutomaton<LETTER, STATE> concurrentPrefixProduct(final INestedWordAutomaton<LETTER, STATE> nwa) {
		// TODO Christian 2017-02-15 Temporary workaround, state factory should become a parameter
		return (new ConcurrentProduct<>(mServices, (IConcurrentProductStateFactory<STATE>) mStateFactory, this, nwa,
				true)).getResult();
	}

	/**
	 * @param state
	 *            A state.
	 * @return the number of incoming internal transitions
	 */
	public int numberOfIncomingInternalTransitions(final STATE state) {
		int result = 0;
		for (final LETTER letter : lettersInternalIncoming(state)) {
			result += predInternal(state, letter).size();
		}
		return result;
	}

	/*
	public InternalTransitions
			getInternalTransitions(IAuxiliaryStateContainer<LETTER, STATE> state,
					LETTER symbol) {
		return new InternalTransitions(state, symbol);
	}

	public InternalTransitions
			getInternalTransitions(IAuxiliaryStateContainer<LETTER, STATE> state) {
		return new InternalTransitions(state);
	}

	public InternalTransitions getInternalTransitions() {
		return new InternalTransitions();
	}

	public class InternalTransition {
		private final IAuxiliaryStateContainer<LETTER, STATE> predecessor;
		private final LETTER symbol;
		private final IAuxiliaryStateContainer<LETTER, STATE> successor;

		public InternalTransition(IAuxiliaryStateContainer<LETTER, STATE> predecessor,
				LETTER symbol,
				IAuxiliaryStateContainer<LETTER, STATE> successor) {
			predecessor = predecessor;
			symbol = symbol;
			successor = successor;
		}

		public IAuxiliaryStateContainer<LETTER, STATE> getPredecessor() {
			return predecessor;
		}

		public LETTER getSymbol() {
			return symbol;
		}

		public IAuxiliaryStateContainer<LETTER, STATE> getSuccessor() {
			return successor;
		}

		public String toString() {
			return "( " + predecessor + " , " + symbol + " , " +
					successor + " )";
		}
	}

	public class InternalTransitions implements Iterable<InternalTransition> {
		private final boolean fixedPredecessor;
		private IAuxiliaryStateContainer<LETTER, STATE> predecessor;
		private final boolean fixedSymbol;
		private LETTER symbol;

		public InternalTransitions(IAuxiliaryStateContainer<LETTER, STATE> state,
				LETTER symbol) {
			fixedPredecessor = true;
			predecessor = state;
			fixedSymbol = true;
			symbol = symbol;
		}

		public InternalTransitions(IAuxiliaryStateContainer<LETTER, STATE> state) {
			fixedPredecessor = true;
			predecessor = state;
			fixedSymbol = false;
		}

		public InternalTransitions() {
			fixedPredecessor = false;
			fixedSymbol = false;
		}

		@Override
		public Iterator<InternalTransition> iterator() {
			return new InternalTransitionIterator();
		}

		public class InternalTransitionIterator implements
				Iterator<InternalTransition> {

			public Iterator<IAuxiliaryStateContainer<LETTER, STATE>> predIterator;
			private Iterator<LETTER> symbolIterator;
			private Iterator<IAuxiliaryStateContainer<LETTER, STATE>> succIterator;

			private boolean finished = false;

			public InternalTransitionIterator() {
				if (fixedSymbol) {
					assert (fixedPredecessor);
					predIterator = null;
					symbolIterator = null;
					succIterator = predecessor.getInternalSucc(symbol).iterator();
					assert (succIterator != null);
				} else {
					if (fixedPredecessor) {
						predIterator = null;
						symbolIterator = predecessor.getSymbolsInternal().iterator();
						assert (symbolIterator != null);
						updateSuccIterator();
						while (!finished && !succIterator.hasNext()) {
							updateSymbolIterator();
						}
					} else {
						predIterator = getAllStates().iterator();
						updateSymbolIterator();
						updateSuccIterator();
						while (!finished && !succIterator.hasNext()) {
							updateSymbolIterator();
						}
					}
				}
			}

			private void updateSuccIterator() {
				if (fixedSymbol) {
					finished = true;
					return;
				} else {
					while (!finished && !symbolIterator.hasNext()) {
						updateSymbolIterator();
					}
					if (finished) {
						return;
					} else {
						assert (symbolIterator.hasNext());
						symbol = symbolIterator.next();
						succIterator = predecessor.getInternalSucc(symbol).iterator();
					}
				}
			}

			private void updateSymbolIterator() {
				if (fixedPredecessor) {
					finished = true;
					return;
				} else {
					if (predIterator.hasNext()) {
						predecessor = predIterator.next();
						symbolIterator = predecessor.getSymbolsInternal().iterator();
					} else {
						finished = true;
					}
				}
			}

			@Override
			public boolean hasNext() {
				if (finished) {
					return false;
				} else {
					return succIterator.hasNext();
				}

			}

			@Override
			public InternalTransition next() {
				IAuxiliaryStateContainer<LETTER, STATE> succ = succIterator.next();
				InternalTransition result =
						new InternalTransition(predecessor, symbol, succ);
				while (!finished && !succIterator.hasNext()) {
					updateSuccIterator();
				}
				return result;
			}
		}
	}
	*/

	@Override
	public String toString() {
		return (new AutomatonDefinitionPrinter<String, String>(mServices, "nwa", Format.ATS, this))
				.getDefinitionAsString();
	}

	/**
	 * Given a nested word (without pending returns) a_0,...,a_n and a sequence of states q_0,...,q_{n+1}, add for each
	 * i
	 * <ul>
	 * <li>the internal transition (q_i, a_i, a_{i+1}) if i is an internal position,
	 * <li>the call transition (q_i, a_i, a_{i+1}) if i is a call position, and
	 * <li>the return transition (q_i, q_k, a_i, a_{i+1}) where k is the corresponding call position. Expects that all
	 * symbols are contained in the alphabets and the all states are contained in the automaton.
	 * </ul>
	 *
	 * @param nestedWord
	 *            nested word
	 * @param stateList
	 *            list of states
	 */
	public void addTransitions(final NestedWord<LETTER> nestedWord, final List<STATE> stateList) {
		assert nestedWord.length() + 1 == stateList.size();
		for (int i = 0; i < nestedWord.length(); i++) {
			final LETTER symbol = nestedWord.getSymbol(i);
			final STATE pred = stateList.get(i);
			final STATE succ = stateList.get(i + 1);

			if (nestedWord.isCallPosition(i)) {
				addCallTransition(pred, symbol, succ);
			} else if (nestedWord.isReturnPosition(i)) {
				assert !nestedWord.isPendingReturn(i);
				final int callPos = nestedWord.getCallPosition(i);
				final STATE hierPred = stateList.get(callPos);
				addReturnTransition(pred, hierPred, symbol, succ);
			} else {
				assert nestedWord.isInternalPosition(i);
				addInternalTransition(pred, symbol, succ);
			}
		}
	}

	@Override
	public void addInternalTransitions(final STATE pred, final LETTER letter, final Collection<STATE> succs) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void addCallTransitions(final STATE pred, final LETTER letter, final Collection<STATE> succs) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void addReturnTransitions(final STATE pred, final STATE hier, final LETTER letter, final Collection<STATE> succs) {
		throw new UnsupportedOperationException();
	}




}
