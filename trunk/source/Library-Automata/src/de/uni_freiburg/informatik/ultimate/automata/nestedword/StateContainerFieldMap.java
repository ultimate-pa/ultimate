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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

/**
 * Contains a {@link STATE} and information of transitions in field/map implementation of NWAs.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class StateContainerFieldMap<LETTER, STATE> {
	private static final int ONE = 1;
	private static final int TWO = 2;
	private static final int THREE = 3;
	private static final int FOUR = 4;

	private final STATE mState;
	private Object mOut1;
	private Object mOut2;
	private Object mOut3;
	// TODO Christian 2016-09-02: This field is unused.
	private Object mOut4;

	/**
	 * Constructor.
	 * 
	 * @param state
	 *            state
	 */
	public StateContainerFieldMap(final STATE state) {
		mState = state;
	}

	/**
	 * @return The state.
	 */
	public STATE getState() {
		return mState;
	}

	private boolean inOutMapMode() {
		return (mOut1 instanceof Map) || (mOut2 instanceof Map) || (mOut3 instanceof Map) || (mOut4 instanceof Map);
	}

	@SuppressWarnings("unchecked")
	private void addOutgoingInternal(final LETTER letter, final STATE succ) {
		final OutgoingInternalTransition<LETTER, STATE> trans = new OutgoingInternalTransition<>(letter, succ);
		if (inOutMapMode()) {
			addInternalTransitionMap((Map<LETTER, Set<STATE>>) mOut1, letter, succ);
		} else if (mOut1 == null) {
			mOut1 = trans;
		} else if (mOut2 == null) {
			mOut2 = trans;
		} else if (mOut3 == null) {
			mOut3 = trans;
		} else {
			switchOutMode();
			addInternalTransitionMap((Map<LETTER, Set<STATE>>) mOut1, letter, succ);
		}
	}

	@SuppressWarnings("unchecked")
	private void switchOutMode() {
		assert mOut1 != null && !(mOut1 instanceof Map);
		assert mOut2 != null && !(mOut2 instanceof Map);
		assert mOut3 != null && !(mOut3 instanceof Map);
		final Object[] outgoings = new Object[] { mOut1, mOut2, mOut3 };
		mOut1 = new HashMap<LETTER, Set<STATE>>();
		mOut2 = new HashMap<LETTER, Set<STATE>>();
		mOut3 = new HashMap<Map<LETTER, STATE>, Set<STATE>>();
		for (final Object out : outgoings) {
			if (out instanceof OutgoingInternalTransition) {
				final OutgoingInternalTransition<LETTER, STATE> internal =
						(OutgoingInternalTransition<LETTER, STATE>) out;
				addInternalTransitionMap((Map<LETTER, Set<STATE>>) mOut1, internal.getLetter(), internal.getSucc());
			} else {
				throw new AssertionError();
			}
		}
	}

	protected Object getOut1() {
		return mOut1;
	}

	protected Object getOut2() {
		return mOut2;
	}

	protected Object getOut3() {
		return mOut3;
	}

	private void addInternalTransitionMap(final Map<LETTER, Set<STATE>> letter2succs, final LETTER letter,
			final STATE succ) {
		Set<STATE> succs = letter2succs.get(letter);
		if (succs == null) {
			succs = new HashSet<>();
			letter2succs.put(letter, succs);
		}
		succs.add(succ);
	}

	/**
	 * @return All internal outgoing transitions in field mode.
	 */
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessorsField() {
		return FieldIterator::new;
	}

	/**
	 * @param letter2succ
	 *            map (letter -> successors)
	 * @param letter
	 *            letter
	 * @return All internal outgoing transitions for a given map and letter.
	 */
	public Iterable<OutgoingInternalTransition<LETTER, STATE>>
			internalSuccessorsMap(final Map<LETTER, Set<STATE>> letter2succ, final LETTER letter) {
		return () -> new MapLetterIterator(letter2succ, letter);
	}

	/**
	 * The resulting {@link Iterator} iterates over all {@link OutgoingInternalTransition}s of the state.
	 * <p>
	 * Implementation detail: It iterates over all outgoing internal letters and uses the iterators returned by
	 * internalSuccessors(state, letter).
	 * 
	 * @param letter2succ
	 *            map (letter -> successors)
	 * @return All internal outgoing transitions for a given map.
	 */
	public Iterable<OutgoingInternalTransition<LETTER, STATE>>
			internalSuccessorsMap(final Map<LETTER, Set<STATE>> letter2succ) {
		return () -> new MapNoLetterIterator(letter2succ);
	}

	/**
	 * Iterator for field mode.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private final class FieldIterator implements Iterator<OutgoingInternalTransition<LETTER, STATE>> {
		/**
		 * Points to next field with {@link OutgoingInternalTransition}.
		 */
		private int mPosition;

		public FieldIterator() {
			updatePosition();
		}

		private void updatePosition() {
			mPosition++;
		}

		@Override
		public boolean hasNext() {
			return mPosition < FOUR;
		}

		@SuppressWarnings("unchecked")
		@Override
		public OutgoingInternalTransition<LETTER, STATE> next() {
			final Object result;
			switch (mPosition) {
				case ONE:
					result = getOut1();
					break;
				case TWO:
					result = getOut2();
					break;
				case THREE:
					result = getOut3();
					break;
				default:
					throw new NoSuchElementException();
			}
			if (!(result instanceof OutgoingInternalTransition)) {
				throw new AssertionError();
			}
			updatePosition();
			return (OutgoingInternalTransition<LETTER, STATE>) result;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}

	/**
	 * Iterator for map mode and a given letter.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private final class MapLetterIterator implements Iterator<OutgoingInternalTransition<LETTER, STATE>> {
		private final LETTER mLetter;
		private Iterator<STATE> mIterator;

		protected MapLetterIterator(final Map<LETTER, Set<STATE>> letter2succ, final LETTER letter) {
			this.mLetter = letter;
			if (letter2succ != null) {
				if (letter2succ.get(letter) != null) {
					mIterator = letter2succ.get(letter).iterator();
				} else {
					mIterator = null;
				}
			} else {
				mIterator = null;
			}
		}

		@Override
		public boolean hasNext() {
			return mIterator == null || mIterator.hasNext();
		}

		@Override
		public OutgoingInternalTransition<LETTER, STATE> next() {
			if (mIterator == null) {
				throw new NoSuchElementException();
			}
			final STATE succ = mIterator.next();
			return new OutgoingInternalTransition<>(mLetter, succ);
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}

	/**
	 * Iterator for map mode and no given letter.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private final class MapNoLetterIterator implements Iterator<OutgoingInternalTransition<LETTER, STATE>> {
		private final Map<LETTER, Set<STATE>> mLetter2succ;
		private final Iterator<LETTER> mLetterIterator;
		private LETTER mCurrentLetter;
		private Iterator<OutgoingInternalTransition<LETTER, STATE>> mCurrentIterator;

		protected MapNoLetterIterator(final Map<LETTER, Set<STATE>> letter2succ) {
			mLetter2succ = letter2succ;
			mLetterIterator = letter2succ.keySet().iterator();
			nextLetter();
		}

		private void nextLetter() {
			if (mLetterIterator.hasNext()) {
				do {
					mCurrentLetter = mLetterIterator.next();
					mCurrentIterator = internalSuccessorsMap(mLetter2succ, mCurrentLetter).iterator();
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
	}
}
