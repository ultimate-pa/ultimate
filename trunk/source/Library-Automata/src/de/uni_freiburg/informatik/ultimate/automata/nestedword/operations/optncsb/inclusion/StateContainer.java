/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

class StateContainer<LETTER, STATE> {
	
	protected final STATE mState;		
	// store outgoing transitions
	private Map<LETTER, Set<STATE>> mInternalOut = new HashMap<>();
	// store incoming transitions
	private Map<LETTER, Set<STATE>> mInternalIn = new HashMap<>();
	
	private final Set<LETTER> mEmptySetOfLetters = new HashSet<>(0);
	
	public StateContainer(STATE state) {
		mState = state;
	}
	
	protected STATE getState() {
		return mState;
	}
	
	protected void addInternalOutgoing(final OutgoingInternalTransition<LETTER, STATE> internalOutgoing) {
		final LETTER letter = internalOutgoing.getLetter();
		final STATE succ = internalOutgoing.getSucc();
		if (mInternalOut == null) {
			mInternalOut = new HashMap<>();
		}
		Set<STATE> succs = mInternalOut.get(letter);
		if (succs == null) {
			succs = new HashSet<>();
			mInternalOut.put(letter, succs);
		}
		succs.add(succ);
	}
	
	protected void addInternalIncoming(final IncomingInternalTransition<LETTER, STATE> internalIncoming) {
		final LETTER letter = internalIncoming.getLetter();
		final STATE pred = internalIncoming.getPred();
		if (mInternalIn == null) {
			mInternalIn = new HashMap<>();
		}
		Set<STATE> preds = mInternalIn.get(letter);
		if (preds == null) {
			preds = new HashSet<>();
			mInternalIn.put(letter, preds);
		}
		preds.add(pred);
	}
	
	protected void removeSuccessor(STATE succ) {
		Map<LETTER, Set<STATE>> outs = new HashMap<>();
		for(Entry<LETTER, Set<STATE>> entry : mInternalOut.entrySet()) {
			Set<STATE> succs = entry.getValue();
			if(succs.contains(succ)) succs.remove(succ);
			if(!succs.isEmpty()) {
				outs.put(entry.getKey(), succs);
			}
		}
		mInternalOut = outs;
	}
	
	protected void removePredecessors(Set<STATE> ps) {
		Map<LETTER, Set<STATE>> ins = new HashMap<>();
		for(Entry<LETTER, Set<STATE>> entry : mInternalIn.entrySet()) {
			Set<STATE> preds = entry.getValue();
			preds.removeAll(ps);
			if(!preds.isEmpty()) {
				ins.put(entry.getKey(), preds);
			}
 		}
		mInternalIn = ins;
	}
	
	protected LETTER getLetterOfSuccessor(STATE succ) {
		for(Entry<LETTER, Set<STATE>> entry : mInternalOut.entrySet()) {
			Set<STATE> succs = entry.getValue();
			if(succs.contains(succ)) return entry.getKey();
		}
		return null;
	}
	
	protected LETTER getLetterOfPredecessor(STATE pred) {
		for(Entry<LETTER, Set<STATE>> entry : mInternalIn.entrySet()) {
			Set<STATE> preds = entry.getValue();
			if(preds.contains(pred)) return entry.getKey();
		}
		return null;
	}
	
	protected boolean hashSelfloop() {
		for(Set<STATE> succs : mInternalOut.values()) {
			if(succs.contains(mState)) return true;
		}
		return false;
	}
	
	public Set<LETTER> lettersInternalIncoming() {
		final Map<LETTER, Set<STATE>> map = mInternalIn;
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors() {
		return () -> new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
			private Iterator<LETTER> mLetterIterator;
			private LETTER mCurrentLetter;
			private Iterator<OutgoingInternalTransition<LETTER, STATE>> mCurrentIterator;

			{
				mLetterIterator = mInternalOut.keySet().iterator();
				nextLetter();
			}

			private void nextLetter() {
				if (mLetterIterator.hasNext()) {
					do {
						mCurrentLetter = mLetterIterator.next();
						mCurrentIterator = internalSuccessors(mCurrentLetter).iterator();
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
			public OutgoingInternalTransition<LETTER, STATE> next() {
				if (mCurrentLetter == null) {
					throw new NoSuchElementException();
				}
				final OutgoingInternalTransition<LETTER, STATE> result = mCurrentIterator.next();
				if (!mCurrentIterator.hasNext()) {
					nextLetter();
				}
				return result;
			}
		};
	}

	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(LETTER letter) {
		return () -> new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
			private final Iterator<STATE> mIterator = initialize();
			private Iterator<STATE> initialize() {
				final Map<LETTER, Set<STATE>> letter2succ = mInternalOut;
				if (letter2succ != null && letter2succ.get(letter) != null) {
					return letter2succ.get(letter).iterator();
				}
				return null;
			}

			@Override
			public boolean hasNext() {
				return mIterator != null && mIterator.hasNext();
			}

			@Override
			public OutgoingInternalTransition<LETTER, STATE> next() {
				if (mIterator == null) {
					throw new NoSuchElementException();
				}
				final STATE succ = mIterator.next();
				return new OutgoingInternalTransition<>(letter, succ);
			}
		};
	}

	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors() {
		return () -> new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
			private Iterator<LETTER> mLetterIterator;
			private LETTER mCurrentLetter;
			private Iterator<IncomingInternalTransition<LETTER, STATE>> mCurrentIterator;

			{
				mLetterIterator = lettersInternalIncoming().iterator();
				nextLetter();
			}

			private void nextLetter() {
				if (mLetterIterator.hasNext()) {
					do {
						mCurrentLetter = mLetterIterator.next();
						mCurrentIterator = internalPredecessors(mCurrentLetter).iterator();
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
			public IncomingInternalTransition<LETTER, STATE> next() {
				if (mCurrentLetter == null) {
					throw new NoSuchElementException();
				}
				final IncomingInternalTransition<LETTER, STATE> result = mCurrentIterator.next();
				if (!mCurrentIterator.hasNext()) {
					nextLetter();
				}
				return result;
			}
		};
	}

	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(LETTER letter) {
		return () -> new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
			private final Iterator<STATE> mIterator = initialize();

			private Iterator<STATE> initialize() {
				final Map<LETTER, Set<STATE>> letter2pred = mInternalIn;
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
	
}

