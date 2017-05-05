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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quad;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Contains STATES and information of transitions.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
@SuppressWarnings("unchecked")
class StateContainerFieldAndMap<LETTER, STATE> extends StateContainer<LETTER, STATE> {
	private static final int ONE = 1;
	private static final int TWO = 2;
	private static final int THREE = 3;
	private static final int FOUR = 4;

	private final Set<LETTER> mEmptySetOfLetters = new HashSet<>(0);
	private final Collection<STATE> mEmptySetOfStates = new HashSet<>(0);

	private Object mOut1;
	private Object mOut2;
	private Object mOut3;
	private Object mIn1;
	private Object mIn2;
	private Object mIn3;

	StateContainerFieldAndMap(final STATE state, final int serialNumber, final HashMap<STATE, Integer> downStates,
			final boolean canHaveOutgoingReturn) {
		super(state, serialNumber, downStates, canHaveOutgoingReturn);
	}

	boolean mapModeOutgoing() {
		return (mOut1 instanceof NestedMap2) || (mOut2 instanceof NestedMap2) || (mOut3 instanceof NestedMap3);
	}

	boolean mapModeIncoming() {
		return (mIn1 instanceof NestedMap2) || (mIn2 instanceof NestedMap2) || (mIn3 instanceof Map);
	}

	private void switchOutgoingToMapMode() {
		assert !mapModeOutgoing();
		final List<Object> transitions = new ArrayList<>(THREE);
		if (mOut1 != null) {
			transitions.add(mOut1);
			mOut1 = null;
		}
		if (mOut2 != null) {
			transitions.add(mOut2);
			mOut2 = null;
		}
		if (mOut3 != null) {
			transitions.add(mOut3);
			mOut3 = null;
		}
		for (final Object trans : transitions) {
			if (trans instanceof OutgoingInternalTransition) {
				addInternalOutgoingMap((OutgoingInternalTransition<LETTER, STATE>) trans);
			} else if (trans instanceof OutgoingCallTransition) {
				addCallOutgoingMap((OutgoingCallTransition<LETTER, STATE>) trans);
			} else if (trans instanceof OutgoingReturnTransition) {
				addReturnOutgoingMap((OutgoingReturnTransition<LETTER, STATE>) trans);
			} else {
				throw new AssertionError();
			}
		}
		assert mapModeOutgoing();
	}

	private void switchIncomingToMapMode() {
		assert !mapModeIncoming();
		final List<Object> transitions = new ArrayList<>(THREE);
		if (mIn1 != null) {
			transitions.add(mIn1);
			mIn1 = null;
		}
		if (mIn2 != null) {
			transitions.add(mIn2);
			mIn2 = null;
		}
		if (mIn3 != null) {
			transitions.add(mIn3);
			mIn3 = null;
		}
		for (final Object trans : transitions) {
			if (trans instanceof IncomingInternalTransition) {
				addInternalIncomingMap((IncomingInternalTransition<LETTER, STATE>) trans);
			} else if (trans instanceof IncomingCallTransition) {
				addCallIncomingMap((IncomingCallTransition<LETTER, STATE>) trans);
			} else if (trans instanceof IncomingReturnTransition) {
				addReturnIncomingMap((IncomingReturnTransition<LETTER, STATE>) trans);
			} else {
				throw new AssertionError();
			}
		}
		assert mapModeIncoming();
	}

	@Override
	void addInternalOutgoing(final OutgoingInternalTransition<LETTER, STATE> trans) {
		if (mapModeOutgoing()) {
			addInternalOutgoingMap(trans);
		} else {
			if (mOut1 == null) {
				mOut1 = trans;
			} else if (mOut2 == null) {
				mOut2 = trans;
			} else if (mOut3 == null && (mOut2 instanceof OutgoingInternalTransition)) {
				mOut3 = trans;
			} else {
				switchOutgoingToMapMode();
				addInternalOutgoingMap(trans);
			}
		}
	}

	@Override
	void addInternalIncoming(final IncomingInternalTransition<LETTER, STATE> trans) {
		if (mapModeIncoming()) {
			addInternalIncomingMap(trans);
		} else {
			if (mIn1 == null) {
				mIn1 = trans;
			} else if (mIn2 == null) {
				mIn2 = trans;
			} else if (mIn3 == null && (mIn2 instanceof IncomingInternalTransition)) {
				mIn3 = trans;
			} else {
				switchIncomingToMapMode();
				addInternalIncomingMap(trans);
			}
		}
	}

	@Override
	void addCallOutgoing(final OutgoingCallTransition<LETTER, STATE> trans) {
		if (mapModeOutgoing()) {
			addCallOutgoingMap(trans);
		} else {
			if (mOut2 == null) {
				mOut2 = trans;
			} else {
				switchOutgoingToMapMode();
				addCallOutgoingMap(trans);
			}
		}
	}

	@Override
	void addCallIncoming(final IncomingCallTransition<LETTER, STATE> trans) {
		if (mapModeIncoming()) {
			addCallIncomingMap(trans);
		} else {
			if (mIn2 == null) {
				mIn2 = trans;
			} else {
				switchIncomingToMapMode();
				addCallIncomingMap(trans);
			}
		}
	}

	@Override
	void addReturnOutgoing(final OutgoingReturnTransition<LETTER, STATE> trans) {
		if (mapModeOutgoing()) {
			addReturnOutgoingMap(trans);
		} else {
			if (mOut3 == null) {
				mOut3 = trans;
			} else {
				switchOutgoingToMapMode();
				addReturnOutgoingMap(trans);
			}
		}
	}

	@Override
	void addReturnIncoming(final IncomingReturnTransition<LETTER, STATE> trans) {
		if (mapModeIncoming()) {
			addReturnIncomingMap(trans);
		} else {
			if (mIn3 == null) {
				mIn3 = trans;
			} else {
				switchIncomingToMapMode();
				addReturnIncomingMap(trans);
			}
		}
	}

	void addInternalOutgoingMap(final OutgoingInternalTransition<LETTER, STATE> internalOutgoing) {
		final LETTER letter = internalOutgoing.getLetter();
		final STATE succ = internalOutgoing.getSucc();
		if (mOut1 == null) {
			mOut1 = new NestedMap2<LETTER, STATE, IsContained>();
		}
		((NestedMap2<LETTER, STATE, IsContained>) mOut1).put(letter, succ, IsContained.IsContained);
	}

	void addInternalIncomingMap(final IncomingInternalTransition<LETTER, STATE> internalIncoming) {
		final LETTER letter = internalIncoming.getLetter();
		final STATE pred = internalIncoming.getPred();
		if (mIn1 == null) {
			mIn1 = new NestedMap2<LETTER, STATE, IsContained>();
		}
		((NestedMap2<LETTER, STATE, IsContained>) mIn1).put(letter, pred, IsContained.IsContained);
	}

	void addCallOutgoingMap(final OutgoingCallTransition<LETTER, STATE> callOutgoing) {
		final LETTER letter = callOutgoing.getLetter();
		final STATE succ = callOutgoing.getSucc();
		if (mOut2 == null) {
			mOut2 = new NestedMap2<LETTER, STATE, IsContained>();
		}
		((NestedMap2<LETTER, STATE, IsContained>) mOut2).put(letter, succ, IsContained.IsContained);
	}

	void addCallIncomingMap(final IncomingCallTransition<LETTER, STATE> callIncoming) {
		final LETTER letter = callIncoming.getLetter();
		final STATE pred = callIncoming.getPred();
		if (mIn2 == null) {
			mIn2 = new NestedMap2<LETTER, STATE, IsContained>();
		}
		((NestedMap2<LETTER, STATE, IsContained>) mIn2).put(letter, pred, IsContained.IsContained);
	}

	void addReturnOutgoingMap(final OutgoingReturnTransition<LETTER, STATE> returnOutgoing) {
		final LETTER letter = returnOutgoing.getLetter();
		final STATE hier = returnOutgoing.getHierPred();
		final STATE succ = returnOutgoing.getSucc();
		if (mOut3 == null) {
			mOut3 = new NestedMap3<STATE, LETTER, STATE, IsContained>();
		}
		((NestedMap3<STATE, LETTER, STATE, IsContained>) mOut3).put(hier, letter, succ, IsContained.IsContained);
	}

	void addReturnIncomingMap(final IncomingReturnTransition<LETTER, STATE> returnIncoming) {
		final LETTER letter = returnIncoming.getLetter();
		final STATE hier = returnIncoming.getHierPred();
		final STATE pred = returnIncoming.getLinPred();
		if (mIn3 == null) {
			mIn3 = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
		}
		Map<STATE, Set<STATE>> hier2preds = ((Map<LETTER, Map<STATE, Set<STATE>>>) mIn3).get(letter);
		if (hier2preds == null) {
			hier2preds = new HashMap<>();
			((Map<LETTER, Map<STATE, Set<STATE>>>) mIn3).put(letter, hier2preds);
		}
		Set<STATE> preds = hier2preds.get(hier);
		if (preds == null) {
			preds = new HashSet<>();
			hier2preds.put(hier, preds);
		}
		preds.add(pred);
	}

	@Override
	public Set<LETTER> lettersInternal() {
		if (mapModeOutgoing()) {
			final NestedMap2<LETTER, STATE, IsContained> map = (NestedMap2<LETTER, STATE, IsContained>) mOut1;
			return map == null ? mEmptySetOfLetters : map.keySet();
		}
		final Set<LETTER> result = new HashSet<>(THREE);
		if (mOut1 instanceof OutgoingInternalTransition) {
			LETTER letter = ((OutgoingInternalTransition<LETTER, STATE>) mOut1).getLetter();
			result.add(letter);
			if (mOut2 instanceof OutgoingInternalTransition) {
				letter = ((OutgoingInternalTransition<LETTER, STATE>) mOut2).getLetter();
				if (!result.contains(letter)) {
					result.add(letter);
				}
				if (mOut3 instanceof OutgoingInternalTransition) {
					letter = ((OutgoingInternalTransition<LETTER, STATE>) mOut3).getLetter();
					if (!result.contains(letter)) {
						result.add(letter);
					}
				}
			}
		}
		return result;
	}

	@Override
	public Set<LETTER> lettersInternalIncoming() {
		if (mapModeIncoming()) {
			final NestedMap2<LETTER, STATE, IsContained> map = (NestedMap2<LETTER, STATE, IsContained>) mIn1;
			return map == null ? mEmptySetOfLetters : map.keySet();
		}
		final Set<LETTER> result = new HashSet<>(THREE);
		if (mIn1 instanceof IncomingInternalTransition) {
			LETTER letter = ((IncomingInternalTransition<LETTER, STATE>) mIn1).getLetter();
			result.add(letter);
			if (mIn2 instanceof IncomingInternalTransition) {
				letter = ((IncomingInternalTransition<LETTER, STATE>) mIn2).getLetter();
				if (!result.contains(letter)) {
					result.add(letter);
				}
				if (mIn3 instanceof IncomingInternalTransition) {
					letter = ((IncomingInternalTransition<LETTER, STATE>) mIn3).getLetter();
					if (!result.contains(letter)) {
						result.add(letter);
					}
				}
			}
		}
		return result;
	}

	@Override
	public Set<LETTER> lettersCall() {
		if (mapModeOutgoing()) {
			final NestedMap2<LETTER, STATE, IsContained> map = (NestedMap2<LETTER, STATE, IsContained>) mOut2;
			return map == null ? mEmptySetOfLetters : map.keySet();
		}
		final Set<LETTER> result = new HashSet<>(1);
		if (mOut2 instanceof OutgoingCallTransition) {
			final LETTER letter = ((OutgoingCallTransition<LETTER, STATE>) mOut2).getLetter();
			result.add(letter);
		}
		return result;
	}

	@Override
	public Set<LETTER> lettersCallIncoming() {
		if (mapModeIncoming()) {
			final NestedMap2<LETTER, STATE, IsContained> map = (NestedMap2<LETTER, STATE, IsContained>) mIn2;
			return map == null ? mEmptySetOfLetters : map.keySet();
		}
		final Set<LETTER> result = new HashSet<>(1);
		if (mIn2 instanceof IncomingCallTransition) {
			final LETTER letter = ((IncomingCallTransition<LETTER, STATE>) mIn2).getLetter();
			result.add(letter);
		}
		return result;
	}

	@Override
	@Deprecated
	public Set<LETTER> lettersReturn() {
		if (mapModeOutgoing()) {
			final NestedMap3<STATE, LETTER, STATE, IsContained> map = (NestedMap3<STATE, LETTER, STATE, IsContained>) mOut3;
			return map == null ? mEmptySetOfLetters : map.projektTo2();
		}
		final Set<LETTER> result = new HashSet<>(1);
		if (mOut3 instanceof OutgoingReturnTransition) {
			final LETTER letter = ((OutgoingReturnTransition<LETTER, STATE>) mOut3).getLetter();
			result.add(letter);
		}
		return result;
	}

	@Override
	public Set<LETTER> lettersReturnIncoming() {
		if (mapModeIncoming()) {
			final Map<LETTER, Map<STATE, Set<STATE>>> map = (Map<LETTER, Map<STATE, Set<STATE>>>) mIn3;
			return map == null ? mEmptySetOfLetters : map.keySet();
		}
		final Set<LETTER> result = new HashSet<>(1);
		if (mIn3 instanceof IncomingReturnTransition) {
			final LETTER letter = ((IncomingReturnTransition<LETTER, STATE>) mIn3).getLetter();
			result.add(letter);
		}
		return result;
	}

	@Override
	public Collection<STATE> succInternal(final LETTER letter) {
		if (mapModeOutgoing()) {
			final NestedMap2<LETTER, STATE, IsContained> map = (NestedMap2<LETTER, STATE, IsContained>) mOut1;
			if (map == null) {
				return mEmptySetOfStates;
			}
			final Map<STATE, IsContained> result = map.get(letter);
			return result == null ? mEmptySetOfStates : result.keySet();
		}
		final Collection<STATE> result = new ArrayList<>(THREE);
		if (properOutgoingInternalTransitionAtPosition1(letter)) {
			final STATE state = ((OutgoingInternalTransition<LETTER, STATE>) mOut1).getSucc();
			result.add(state);
		}
		if (properOutgoingInternalTransitionAtPosition2(letter)) {
			final STATE state = ((OutgoingInternalTransition<LETTER, STATE>) mOut2).getSucc();
			if (!result.contains(state)) {
				result.add(state);
			}
		}
		if (properOutgoingInternalTransitionAtPosition3(letter)) {
			final STATE state = ((OutgoingInternalTransition<LETTER, STATE>) mOut3).getSucc();
			if (!result.contains(state)) {
				result.add(state);
			}
		}
		return result;
	}

	@Override
	public Collection<STATE> predInternal(final LETTER letter) {
		if (mapModeIncoming()) {
			final NestedMap2<LETTER, STATE, IsContained> map = (NestedMap2<LETTER, STATE, IsContained>) mIn1;
			if (map == null) {
				return mEmptySetOfStates;
			}
			final Map<STATE, IsContained> result = map.get(letter);
			return result == null ? mEmptySetOfStates : result.keySet();
		}
		final Collection<STATE> result = new ArrayList<>(THREE);
		if (properIncomingInternalTransitionAtPosition1(letter)) {
			final STATE state = ((IncomingInternalTransition<LETTER, STATE>) mIn1).getPred();
			result.add(state);
		}
		if (properIncomingInternalTransitionAtPosition2(letter)) {
			final STATE state = ((IncomingInternalTransition<LETTER, STATE>) mIn2).getPred();
			if (!result.contains(state)) {
				result.add(state);
			}
		}
		if (properIncomingInternalTransitionAtPosition3(letter)) {
			final STATE state = ((IncomingInternalTransition<LETTER, STATE>) mIn3).getPred();
			if (!result.contains(state)) {
				result.add(state);
			}
		}
		return result;
	}

	@Override
	public Collection<STATE> succCall(final LETTER letter) {
		if (mapModeOutgoing()) {
			final NestedMap2<LETTER, STATE, IsContained> map = (NestedMap2<LETTER, STATE, IsContained>) mOut2;
			if (map == null) {
				return mEmptySetOfStates;
			}
			final Map<STATE, IsContained> result = map.get(letter);
			return result == null ? mEmptySetOfStates : result.keySet();
		}
		final Collection<STATE> result = new ArrayList<>(1);
		if (properOutgoingCallTransitionAtPosition2(letter)) {
			final STATE state = ((OutgoingCallTransition<LETTER, STATE>) mOut2).getSucc();
			result.add(state);
		}
		return result;
	}

	@Override
	public Collection<STATE> predCall(final LETTER letter) {
		if (mapModeIncoming()) {
			final NestedMap2<LETTER, STATE, IsContained> map = (NestedMap2<LETTER, STATE, IsContained>) mIn2;
			if (map == null) {
				return mEmptySetOfStates;
			}
			final Map<STATE, IsContained> result = map.get(letter);
			return result == null ? mEmptySetOfStates : result.keySet();
		}
		final Collection<STATE> result = new ArrayList<>(1);
		if (properIncomingCallTransitionAtPosition2(letter)) {
			final STATE state = ((IncomingCallTransition<LETTER, STATE>) mIn2).getPred();
			result.add(state);
		}
		return result;
	}

	@Override
	public Collection<STATE> hierPred(final LETTER letter) {
		if (mapModeOutgoing()) {
			final NestedMap3<STATE, LETTER, STATE, IsContained> map = (NestedMap3<STATE, LETTER, STATE, IsContained>) mOut3;
			if (map == null) {
				return mEmptySetOfStates;
			}
			final Set<STATE> result = new HashSet<>();
			for (final Quad<STATE, LETTER, STATE, IsContained> entry : map.entrySet()) {
				if (letter.equals(entry.getSecond())) {
					result.add(entry.getFirst());
				}
			}
			return result;
		}
		final Collection<STATE> result = new ArrayList<>(1);
		if (properOutgoingReturnTransitionAtPosition3(null, letter)) {
			final STATE state = ((OutgoingReturnTransition<LETTER, STATE>) mOut3).getHierPred();
			result.add(state);
		}
		return result;
	}

	@Override
	public Collection<STATE> succReturn(final STATE hier, final LETTER letter) {
		if (mapModeOutgoing()) {
			final NestedMap3<STATE, LETTER, STATE, IsContained> map = (NestedMap3<STATE, LETTER, STATE, IsContained>) mOut3;
			if (map == null) {
				return mEmptySetOfStates;
			}
			final Map<STATE, IsContained> result = map.get(hier, letter);
			return result == null ? mEmptySetOfStates : result.keySet();
		}
		final Collection<STATE> result = new ArrayList<>(1);
		if (properOutgoingReturnTransitionAtPosition3(hier, letter)) {
			final STATE state = ((OutgoingReturnTransition<LETTER, STATE>) mOut3).getSucc();
			result.add(state);
		}
		return result;
	}

	@Override
	public Collection<STATE> predReturnLin(final LETTER letter, final STATE hier) {
		if (mapModeIncoming()) {
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = (Map<LETTER, Map<STATE, Set<STATE>>>) mIn3;
			if (letter2hier2preds == null) {
				return mEmptySetOfStates;
			}
			final Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
			if (hier2preds == null) {
				return mEmptySetOfStates;
			}
			final Set<STATE> result = hier2preds.get(hier);
			return result == null ? mEmptySetOfStates : result;
		}
		final Collection<STATE> result = new ArrayList<>(1);
		if (properIncomingReturnTransitionAtPosition3(hier, letter)) {
			final STATE state = ((IncomingReturnTransition<LETTER, STATE>) mIn3).getLinPred();
			result.add(state);
		}
		return result;
	}

	@Override
	public Collection<STATE> predReturnHier(final LETTER letter) {
		if (mapModeIncoming()) {
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = (Map<LETTER, Map<STATE, Set<STATE>>>) mIn3;
			if (letter2hier2preds == null) {
				return mEmptySetOfStates;
			}
			final Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
			if (hier2preds == null) {
				return mEmptySetOfStates;
			}
			return hier2preds.keySet();
		}
		final Collection<STATE> result = new ArrayList<>(1);
		if (properIncomingReturnTransitionAtPosition3(null, letter)) {
			final STATE state = ((IncomingReturnTransition<LETTER, STATE>) mIn3).getHierPred();
			result.add(state);
		}
		return result;
	}

	private Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessorsMap(final LETTER letter) {
		assert mapModeIncoming();
		if (mIn1 == null) {
			return Collections.emptySet();
		} else {
			final Function<STATE, IncomingInternalTransition<LETTER, STATE>> transformer = x -> new IncomingInternalTransition<LETTER, STATE>(
					x, letter);
			return () -> new TransformIterator<STATE, IncomingInternalTransition<LETTER, STATE>>(
					keySetOrEmpty(((NestedMap2<LETTER, STATE, IsContained>) mIn1).get(letter)).iterator(), transformer);
		}
	}

	private Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessorsMap() {
		assert mapModeIncoming();
		if (mIn1 == null) {
			return Collections.emptySet();
		} else {
			return () -> new TransformIterator<Triple<LETTER, STATE, IsContained>, IncomingInternalTransition<LETTER, STATE>>(
					((NestedMap2<LETTER, STATE, IsContained>) mIn1).entrySet().iterator(),
					x -> new IncomingInternalTransition<LETTER, STATE>(x.getSecond(), x.getFirst()));
		}
	}

	private Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessorsMap(final LETTER letter) {
		assert mapModeIncoming();
		if (mIn2 == null) {
			return Collections.emptySet();
		} else {
			final Function<STATE, IncomingCallTransition<LETTER, STATE>> transformer = x -> new IncomingCallTransition<LETTER, STATE>(
					x, letter);
			return () -> new TransformIterator<STATE, IncomingCallTransition<LETTER, STATE>>(
					keySetOrEmpty(((NestedMap2<LETTER, STATE, IsContained>) mIn2).get(letter)).iterator(), transformer);
		}
	}

	private Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessorsMap() {
		assert mapModeIncoming();
		if (mIn2 == null) {
			return Collections.emptySet();
		} else {
			return () -> new TransformIterator<Triple<LETTER, STATE, IsContained>, IncomingCallTransition<LETTER, STATE>>(
					((NestedMap2<LETTER, STATE, IsContained>) mIn2).entrySet().iterator(),
					x -> new IncomingCallTransition<LETTER, STATE>(x.getSecond(), x.getFirst()));
		}
	}

	private Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessorsMap(final STATE hier,
			final LETTER letter) {
		assert mapModeIncoming();
		return () -> new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
			private final Iterator<STATE> mIterator = initialize();

			private Iterator<STATE> initialize() {
				final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = (Map<LETTER, Map<STATE, Set<STATE>>>) mIn3;
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

	private Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessorsMap(final LETTER letter) {
		assert mapModeIncoming();
		/**
		 * Iterates over all IncomingReturnTransition of succ. Iterates over all incoming return letters and uses the
		 * iterators returned by returnPredecessorsMap(hier, letter, succ)
		 */
		return () -> new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
			private Iterator<STATE> mHierIterator;
			private STATE mCurrentHier;
			private Iterator<IncomingReturnTransition<LETTER, STATE>> mCurrentIterator;

			{
				mHierIterator = predReturnHier(letter).iterator();
				nextHier();
			}

			private void nextHier() {
				if (mHierIterator.hasNext()) {
					do {
						mCurrentHier = mHierIterator.next();
						mCurrentIterator = returnPredecessorsMap(mCurrentHier, letter).iterator();
					} while (!mCurrentIterator.hasNext() && mHierIterator.hasNext());
					if (!mCurrentIterator.hasNext()) {
						mCurrentHier = null;
						mCurrentIterator = null;
					}
				} else {
					mCurrentHier = null;
					mCurrentIterator = null;
				}
			}

			@Override
			public boolean hasNext() {
				return mCurrentHier != null;
			}

			@Override
			public IncomingReturnTransition<LETTER, STATE> next() {
				if (mCurrentHier == null) {
					throw new NoSuchElementException();
				}
				final IncomingReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
				if (!mCurrentIterator.hasNext()) {
					nextHier();
				}
				return result;
			}
		};
	}

	private Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessorsMap() {
		assert mapModeIncoming();
		/**
		 * Iterates over all IncomingReturnTransition of succ. Iterates over all incoming return letters and uses the
		 * iterators returned by returnPredecessorsMap(letter, succ)
		 */
		return () -> new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
			private Iterator<LETTER> mLetterIterator;
			private LETTER mCurrentLetter;
			private Iterator<IncomingReturnTransition<LETTER, STATE>> mCurrentIterator;

			{
				mLetterIterator = lettersReturnIncoming().iterator();
				nextLetter();
			}

			private void nextLetter() {
				if (mLetterIterator.hasNext()) {
					do {
						mCurrentLetter = mLetterIterator.next();
						mCurrentIterator = returnPredecessorsMap(mCurrentLetter).iterator();
					} while (!mCurrentIterator.hasNext() && mLetterIterator.hasNext());
					if (!mCurrentIterator.hasNext()) {
						mCurrentLetter = null;
						mCurrentIterator = null;
					}
				} else {
					mCurrentLetter = null;
					mCurrentIterator = null;
				}
			}

			@Override
			public boolean hasNext() {
				return mCurrentLetter != null;
			}

			@Override
			public IncomingReturnTransition<LETTER, STATE> next() {
				if (mCurrentLetter == null) {
					throw new NoSuchElementException();
				}
				final IncomingReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
				if (!mCurrentIterator.hasNext()) {
					nextLetter();
				}
				return result;
			}
		};
	}

	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessorsMap(final LETTER letter) {
		assert mapModeOutgoing();
		if (mOut1 == null) {
			return Collections.emptySet();
		} else {
			final Function<STATE, OutgoingInternalTransition<LETTER, STATE>> transformer = x -> new OutgoingInternalTransition<>(
					letter, x);
			return () -> new TransformIterator<STATE, OutgoingInternalTransition<LETTER, STATE>>(
					keySetOrEmpty(((NestedMap2<LETTER, STATE, IsContained>) mOut1).get(letter)).iterator(),
					transformer);
		}
	}

	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessorsMap() {
		assert mapModeOutgoing();
		if (mOut1 == null) {
			return Collections.emptySet();
		} else {
			return () -> new TransformIterator<Triple<LETTER, STATE, IsContained>, OutgoingInternalTransition<LETTER, STATE>>(
					((NestedMap2<LETTER, STATE, IsContained>) mOut1).entrySet().iterator(),
					x -> new OutgoingInternalTransition<LETTER, STATE>(x.getFirst(), x.getSecond()));
		}
	}

	private Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessorsMap(final LETTER letter) {
		assert mapModeOutgoing();
		if (mOut2 == null) {
			return Collections.emptySet();
		} else {
			final Function<STATE, OutgoingCallTransition<LETTER, STATE>> transformer = x -> new OutgoingCallTransition<>(
					letter, x);
			return () -> new TransformIterator<STATE, OutgoingCallTransition<LETTER, STATE>>(
					keySetOrEmpty(((NestedMap2<LETTER, STATE, IsContained>) mOut2).get(letter)).iterator(),
					transformer);
		}
	}

	private Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessorsMap() {
		assert mapModeOutgoing();
		if (mOut2 == null) {
			return Collections.emptySet();
		} else {
			return () -> new TransformIterator<Triple<LETTER, STATE, IsContained>, OutgoingCallTransition<LETTER, STATE>>(
					((NestedMap2<LETTER, STATE, IsContained>) mOut2).entrySet().iterator(),
					x -> new OutgoingCallTransition<LETTER, STATE>(x.getFirst(), x.getSecond()));
		}
	}

	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsMap(final STATE hier,
			final LETTER letter) {
		assert mapModeOutgoing();
		if (mOut3 == null) {
			return Collections.emptySet();
		} else {
			final Function<Quad<STATE, LETTER, STATE, IsContained>, OutgoingReturnTransition<LETTER, STATE>> transformer = 
					x -> new OutgoingReturnTransition<>(x.getFirst(), x.getSecond(), x.getThird());
					return () -> new TransformIterator<Quad<STATE, LETTER, STATE, IsContained>, OutgoingReturnTransition<LETTER, STATE>>(
							((NestedMap3<STATE, LETTER, STATE, IsContained>) mOut3).entries(hier, letter).iterator(), transformer);
		}
	}

	@Deprecated
	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsMap(final LETTER letter) {
		assert mapModeOutgoing();
		/**
		 * Iterates over all OutgoingReturnTransition of state. Iterates over all outgoing return letters and uses the
		 * iterators returned by returnSuccecessorsMap(state, letter)
		 */
		return () -> new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
			private Iterator<STATE> mHierIterator;
			private STATE mCurrentHier;
			private Iterator<OutgoingReturnTransition<LETTER, STATE>> mCurrentIterator;

			{
				mHierIterator = hierPred(letter).iterator();
				nextHier();
			}

			private void nextHier() {
				if (mHierIterator.hasNext()) {
					do {
						mCurrentHier = mHierIterator.next();
						mCurrentIterator = returnSuccessorsMap(mCurrentHier, letter).iterator();
					} while (!mCurrentIterator.hasNext() && mHierIterator.hasNext());
					if (!mCurrentIterator.hasNext()) {
						mCurrentHier = null;
						mCurrentIterator = null;
					}
				} else {
					mCurrentHier = null;
					mCurrentIterator = null;
				}
			}

			@Override
			public boolean hasNext() {
				return mCurrentHier != null;
			}

			@Override
			public OutgoingReturnTransition<LETTER, STATE> next() {
				if (mCurrentHier == null) {
					throw new NoSuchElementException();
				}
				final OutgoingReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
				if (!mCurrentIterator.hasNext()) {
					nextHier();
				}
				return result;
			}
		};
	}

	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsMap() {
		assert mapModeOutgoing();
		if (mOut3 == null) {
			return Collections.emptySet();
		} else {
			final Function<Quad<STATE, LETTER, STATE, IsContained>, OutgoingReturnTransition<LETTER, STATE>> transformer = 
					x -> new OutgoingReturnTransition<>(x.getFirst(), x.getSecond(), x.getThird());
					return () -> new TransformIterator<Quad<STATE, LETTER, STATE, IsContained>, OutgoingReturnTransition<LETTER, STATE>>(
							((NestedMap3<STATE, LETTER, STATE, IsContained>) mOut3).entrySet().iterator(), transformer);
		}
	}

	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHierMap(final STATE hier) {
		assert mapModeOutgoing();
		if (mOut3 == null) {
			return Collections.emptySet();
		} else {
			final Function<Quad<STATE, LETTER, STATE, IsContained>, OutgoingReturnTransition<LETTER, STATE>> transformer = 
					x -> new OutgoingReturnTransition<>(x.getFirst(), x.getSecond(), x.getThird());
					return () -> new TransformIterator<Quad<STATE, LETTER, STATE, IsContained>, OutgoingReturnTransition<LETTER, STATE>>(
							((NestedMap3<STATE, LETTER, STATE, IsContained>) mOut3).entries(hier).iterator(), transformer);
		}
	}

	boolean properOutgoingInternalTransitionAtPosition1(final LETTER letter) {
		return (mOut1 instanceof OutgoingInternalTransition)
				&& (letter == null || letter.equals(((OutgoingInternalTransition<LETTER, STATE>) mOut1).getLetter()));
	}

	boolean properOutgoingInternalTransitionAtPosition2(final LETTER letter) {
		return (mOut2 instanceof OutgoingInternalTransition)
				&& (letter == null || letter.equals(((OutgoingInternalTransition<LETTER, STATE>) mOut2).getLetter()));
	}

	boolean properOutgoingInternalTransitionAtPosition3(final LETTER letter) {
		return (mOut3 instanceof OutgoingInternalTransition)
				&& (letter == null || letter.equals(((OutgoingInternalTransition<LETTER, STATE>) mOut3).getLetter()));
	}

	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessorsField(final LETTER letter) {
		return () -> new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
			/**
			 * Points to next field that has OutgoingInternalTransition.
			 */
			private int mPosition;

			{
				mPosition = 0;
				updatePosition();
			}

			private void updatePosition() {
				mPosition++;
				while (mPosition < FOUR) {
					if ((mPosition == ONE && properOutgoingInternalTransitionAtPosition1(letter))
							|| (mPosition == TWO && properOutgoingInternalTransitionAtPosition2(letter))
							|| (mPosition == THREE && properOutgoingInternalTransitionAtPosition3(letter))) {
						return;
					}
					mPosition++;
				}
			}

			@Override
			public boolean hasNext() {
				return mPosition < FOUR;
			}

			@Override
			public OutgoingInternalTransition<LETTER, STATE> next() {
				Object result;
				if (mPosition == ONE) {
					result = mOut1;
				} else if (mPosition == TWO) {
					result = mOut2;
				} else if (mPosition == THREE) {
					result = mOut3;
				} else {
					throw new NoSuchElementException();
				}
				updatePosition();
				return (OutgoingInternalTransition<LETTER, STATE>) result;
			}
		};
	}

	boolean properIncomingInternalTransitionAtPosition1(final LETTER letter) {
		return (mIn1 instanceof IncomingInternalTransition)
				&& (letter == null || letter.equals(((IncomingInternalTransition<LETTER, STATE>) mIn1).getLetter()));
	}

	boolean properIncomingInternalTransitionAtPosition2(final LETTER letter) {
		return (mIn2 instanceof IncomingInternalTransition)
				&& (letter == null || letter.equals(((IncomingInternalTransition<LETTER, STATE>) mIn2).getLetter()));
	}

	boolean properIncomingInternalTransitionAtPosition3(final LETTER letter) {
		return (mIn3 instanceof IncomingInternalTransition)
				&& (letter == null || letter.equals(((IncomingInternalTransition<LETTER, STATE>) mIn3).getLetter()));
	}

	private Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessorsField(final LETTER letter) {
		return () -> new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
			/**
			 * Points to next field that has IncomingInternalTransition.
			 */
			private short mPosition;

			{
				mPosition = 0;
				updatePosition();
			}

			private void updatePosition() {
				mPosition++;
				while (mPosition < FOUR) {
					if ((mPosition == ONE && properIncomingInternalTransitionAtPosition1(letter))
							|| (mPosition == TWO && properIncomingInternalTransitionAtPosition2(letter))
							|| (mPosition == THREE && properIncomingInternalTransitionAtPosition3(letter))) {
						return;
					}
					mPosition++;
				}
			}

			@Override
			public boolean hasNext() {
				return mPosition < FOUR;
			}

			@Override
			public IncomingInternalTransition<LETTER, STATE> next() {
				Object result;
				if (mPosition == ONE) {
					result = mIn1;
				} else if (mPosition == TWO) {
					result = mIn2;
				} else if (mPosition == THREE) {
					result = mIn3;
				} else {
					throw new NoSuchElementException();
				}
				updatePosition();
				return (IncomingInternalTransition<LETTER, STATE>) result;
			}
		};
	}

	private boolean properOutgoingCallTransitionAtPosition2(final LETTER letter) {
		return (mOut2 instanceof OutgoingCallTransition)
				&& (letter == null || letter.equals(((OutgoingCallTransition<LETTER, STATE>) mOut2).getLetter()));
	}

	private boolean properIncomingCallTransitionAtPosition2(final LETTER letter) {
		return (mIn2 instanceof IncomingCallTransition)
				&& (letter == null || letter.equals(((IncomingCallTransition<LETTER, STATE>) mIn2).getLetter()));
	}

	private boolean properOutgoingReturnTransitionAtPosition3(final STATE hier, final LETTER letter) {
		return (mOut3 instanceof OutgoingReturnTransition)
				&& (hier == null || hier.equals(((OutgoingReturnTransition<LETTER, STATE>) mOut3).getHierPred()))
				&& (letter == null || letter.equals(((OutgoingReturnTransition<LETTER, STATE>) mOut3).getLetter()));
	}

	private boolean properIncomingReturnTransitionAtPosition3(final STATE hier, final LETTER letter) {
		return (mIn3 instanceof IncomingReturnTransition)
				&& (hier == null || hier.equals(((IncomingReturnTransition<LETTER, STATE>) mIn3).getHierPred()))
				&& (letter == null || letter.equals(((IncomingReturnTransition<LETTER, STATE>) mIn3).getLetter()));
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final LETTER letter) {
		if (mapModeOutgoing()) {
			return callSuccessorsMap(letter);
		}
		final ArrayList<OutgoingCallTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properOutgoingCallTransitionAtPosition2(letter)) {
			result.add((OutgoingCallTransition<LETTER, STATE>) mOut2);
		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors() {
		if (mapModeOutgoing()) {
			return callSuccessorsMap();
		}
		final ArrayList<OutgoingCallTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properOutgoingCallTransitionAtPosition2(null)) {
			result.add((OutgoingCallTransition<LETTER, STATE>) mOut2);
		}
		return result;
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final LETTER letter) {
		if (mapModeIncoming()) {
			return callPredecessorsMap(letter);
		}
		final ArrayList<IncomingCallTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properIncomingCallTransitionAtPosition2(letter)) {
			result.add((IncomingCallTransition<LETTER, STATE>) mIn2);
		}
		return result;
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors() {
		if (mapModeIncoming()) {
			return callPredecessorsMap();
		}
		final ArrayList<IncomingCallTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properIncomingCallTransitionAtPosition2(null)) {
			result.add((IncomingCallTransition<LETTER, STATE>) mIn2);
		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE hier, final LETTER letter) {
		if (mapModeOutgoing()) {
			return returnSuccessorsMap(hier, letter);
		}
		final ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properOutgoingReturnTransitionAtPosition3(hier, letter)) {
			result.add((OutgoingReturnTransition<LETTER, STATE>) mOut3);
		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final LETTER letter) {
		if (mapModeOutgoing()) {
			return returnSuccessorsMap(letter);
		}
		final ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properOutgoingReturnTransitionAtPosition3(null, letter)) {
			result.add((OutgoingReturnTransition<LETTER, STATE>) mOut3);
		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors() {
		if (mapModeOutgoing()) {
			return returnSuccessorsMap();
		}
		final ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properOutgoingReturnTransitionAtPosition3(null, null)) {
			result.add((OutgoingReturnTransition<LETTER, STATE>) mOut3);
		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE hier) {
		if (mapModeOutgoing()) {
			return returnSuccessorsGivenHierMap(hier);
		}
		final ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properOutgoingReturnTransitionAtPosition3(hier, null)) {
			result.add((OutgoingReturnTransition<LETTER, STATE>) mOut3);
		}
		return result;
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE hier, final LETTER letter) {
		if (mapModeIncoming()) {
			return returnPredecessorsMap(hier, letter);
		}
		final ArrayList<IncomingReturnTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properIncomingReturnTransitionAtPosition3(hier, letter)) {
			result.add((IncomingReturnTransition<LETTER, STATE>) mIn3);
		}
		return result;
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final LETTER letter) {
		if (mapModeIncoming()) {
			return returnPredecessorsMap(letter);
		}
		final ArrayList<IncomingReturnTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properIncomingReturnTransitionAtPosition3(null, letter)) {
			result.add((IncomingReturnTransition<LETTER, STATE>) mIn3);
		}
		return result;
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors() {
		if (mapModeIncoming()) {
			return returnPredecessorsMap();
		}
		final ArrayList<IncomingReturnTransition<LETTER, STATE>> result = new ArrayList<>(1);
		if (properIncomingReturnTransitionAtPosition3(null, null)) {
			result.add((IncomingReturnTransition<LETTER, STATE>) mIn3);
		}
		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final LETTER letter) {
		if (mapModeOutgoing()) {
			return internalSuccessorsMap(letter);
		}
		return internalSuccessorsField(letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors() {
		if (mapModeOutgoing()) {
			return internalSuccessorsMap();
		}
		return internalSuccessorsField(null);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final LETTER letter) {
		if (mapModeIncoming()) {
			return internalPredecessorsMap(letter);
		}
		return internalPredecessorsField(letter);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors() {
		if (mapModeIncoming()) {
			return internalPredecessorsMap();
		}
		return internalPredecessorsField(null);
	}
	
	private Iterable<STATE> keySetOrEmpty(final Map<STATE, IsContained> map) {
		if (map == null) {
			return Collections.emptySet();
		} else {
			return map.keySet();
		}
	}
}
