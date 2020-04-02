/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.dawg;

import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * Conceptually, a Dawg of depth n is a map from LETTER^n to VALUE. It is implemented as a Map from LETTER to a sub dawg
 * of depth n-1, that gives the mapping for the remaining LETTERS.
 *
 * @author Alexander Nutz, Jochen Hoenicke
 *
 */
public class Dawg<LETTER, VALUE> {
	final VALUE mFinal;
	/**
	 * The transition map. This looks somehow reverse as it maps from destination state to set of letters. But this
	 * makes it easier to unify transitions going to the same state.
	 */
	final Map<LETTER, Dawg<LETTER, VALUE>> mTransitions;
	final Dawg<LETTER, VALUE> mElseTransition;

	final static UnifyHash<Dawg<?, ?>> sUnifier = new UnifyHash<>();

	/**
	 * The dawg that is one level deeper than this and maps every first letter to this Dawg.
	 */
	Dawg<LETTER, VALUE> mCachedParent = null;

	/**
	 * Create a Dawg of depth 0 that maps the empty word to value.
	 * @param value the mapped value.
	 */
	private Dawg(final VALUE value) {
		mFinal = value;
		mTransitions = null;
		mElseTransition = null;
	}

	/**
	 * Create a Dawg of depth n with the given transitions.
	 */
	private Dawg(final Map<LETTER, Dawg<LETTER, VALUE>> transitions, Dawg<LETTER, VALUE> elseTransition) {
		mFinal = null;
		mTransitions = transitions;
		mElseTransition = elseTransition;
	}

	/**
	 * Create a Dawg that maps each word of length {@code levels} to {@code value}.
	 * 
	 * @param levels
	 *            the length of the key words.
	 * @param value
	 *            the mapped value.
	 * @return the constant Dawg.
	 */
	@SuppressWarnings("unchecked")
	public static <LETTER, VALUE> Dawg<LETTER, VALUE> createConst(int levels, final VALUE value) {
		int hash = value.hashCode();
		Dawg<LETTER, VALUE> constDawg = null;
		for (Dawg<?, ?> dawg : sUnifier.iterateHashCode(hash)) {
			if (dawg.isFinal() && dawg.mFinal.equals(value)) {
				constDawg = (Dawg<LETTER, VALUE>) dawg;
				break;
			}
		}
		if (constDawg == null) {
			constDawg = new Dawg<>(value);
			sUnifier.put(hash, constDawg);
		}
		for (int i = 0; i < levels; i++) {
			constDawg = constDawg.createParent();
		}
		return constDawg;
	}

	/**
	 * Create the dawg that is one level deeper than this and maps every first letter to this Dawg. Equivalent to
	 * {@code createDawg(Collections.emptyMap(), this)}.
	 * 
	 * @return the created Dawg.
	 */
	private Dawg<LETTER, VALUE> createParent() {
		if (mCachedParent == null) {
			mCachedParent = new Dawg<>(Collections.emptyMap(), this);
		}
		return mCachedParent;
	}

	/**
	 * Create the dawg with the given transitions.
	 * @param transitions map from LETTER to next Dawgs.
	 * @param elseTransition destination of the default transitition.
	 * 
	 * @return the created Dawg.
	 */
	public static <LETTER, VALUE> Dawg<LETTER, VALUE> createDawg(Map<LETTER, Dawg<LETTER, VALUE>> transitions,
			Dawg<LETTER, VALUE> elseTransition) {
		if (transitions.isEmpty()) {
			return elseTransition.createParent();
		}
		Dawg<LETTER, VALUE> dawg = new Dawg<>(transitions, elseTransition);
		return dawg;
	}

	/**
	 * Create a copy of current Dawg and insert the given key-value pair.
	 * 
	 * @param key
	 *            The key to insert. null-entries correspond to default case.
	 * @param value
	 *            The value to insert.
	 * @return the new Dawg which maps key to value and behaves like this otherwise.
	 */
	public Dawg<LETTER, VALUE> insert(final List<LETTER> key, final VALUE value) {
		/* check if there is nothing to do */
		if (this.getValue(key) == value) {
			return this;
		}
		return insert(key, value, 0);
	}

	private Dawg<LETTER, VALUE> insert(final List<LETTER> key, final VALUE value, int offset) {
		if (offset == key.size()) {
			return createConst(0, value);
		} else {
			LETTER firstLetter = key.get(offset);
			HashMap<LETTER, Dawg<LETTER, VALUE>> newTransitions = new LinkedHashMap<>();
			if (firstLetter == null) {
				Dawg<LETTER, VALUE> elseDest = mElseTransition.insert(key, value, offset + 1);
				for (Map.Entry<LETTER, Dawg<LETTER, VALUE>> oldTrans : mTransitions.entrySet()) {
					Dawg<LETTER, VALUE> newDest = oldTrans.getValue().insert(key, value, offset + 1);
					if (newDest != elseDest) {
						newTransitions.put(oldTrans.getKey(), newDest);
					}
				}
				return createDawg(newTransitions, elseDest);
			} else {
				Dawg<LETTER, VALUE> tailDawg = getNextDawg(firstLetter);
				Dawg<LETTER, VALUE> newTailDawg = tailDawg.insert(key, value, offset + 1);
				newTransitions.putAll(mTransitions);
				if (newTailDawg == mElseTransition) {
					/* new Destination is the default transitions, so remove it from the transition map */
					newTransitions.remove(firstLetter);
				} else {
					newTransitions.put(firstLetter, newTailDawg);
				}
				return createDawg(newTransitions, mElseTransition);
			}
		}
	}

	private <V2, V3> Dawg<LETTER, V3> combineInternal(final Dawg<LETTER, V2> other,
			final BiFunction<VALUE, V2, V3> combinator,
			final Map<Pair<Dawg<LETTER, VALUE>, Dawg<LETTER, V2>>, Dawg<LETTER, V3>> cache) {
		Pair<Dawg<LETTER, VALUE>, Dawg<LETTER, V2>> pair = new Pair<>(this, other);
		Dawg<LETTER, V3> result = cache.get(pair);
		if (result != null) {
			return result;
		}
		if (mElseTransition == null) {
			assert other.mElseTransition == null;
			// both inputs take empty words.
			result = createConst(0, combinator.apply(mFinal, other.mFinal));
		} else {
			Dawg<LETTER, V3> elseCase = mElseTransition.combineInternal(other.mElseTransition, combinator, cache);
			if (mTransitions.isEmpty() && other.mTransitions.isEmpty()) {
				result = elseCase.createParent();
			} else {
				Map<LETTER, Dawg<LETTER, V3>> newTransitions = new LinkedHashMap<>();
				for (Map.Entry<LETTER, Dawg<LETTER, VALUE>> entry : mTransitions.entrySet()) {
					LETTER key = entry.getKey();
					Dawg<LETTER, V3> combined =
							entry.getValue().combineInternal(other.getNextDawg(key), combinator, cache);
					if (combined != elseCase) {
						newTransitions.put(key, combined);
					}
				}
				for (Map.Entry<LETTER, Dawg<LETTER, V2>> entry : other.mTransitions.entrySet()) {
					LETTER key = entry.getKey();
					/* add all remaining keys that are not in the first transition set */
					if (!mTransitions.containsKey(key)) {
						Dawg<LETTER, V3> combined = mElseTransition.combineInternal(entry.getValue(), combinator,
								cache);
						if (combined != elseCase) {
							newTransitions.put(key, combined);
						}
					}
				}
				result = createDawg(newTransitions, elseCase);
			}
		}
		cache.put(pair, result);
		return result;
	}

	/**
	 * Combine two dawgs (this and other) to a new dawg that uses the given combinator function to map each value pair
	 * to a new value. This creates a dawg that maps each key to
	 * {@code combinator.apply(this.getValue(key), other.getValue(key))}.
	 * 
	 * @param other
	 *            the second Dawg.
	 * @param combinator
	 *            the combinator function.
	 * @return the mapped dawg.
	 */
	public <V2, V3> Dawg<LETTER, V3> combine(final Dawg<LETTER, V2> other, final BiFunction<VALUE, V2, V3> combinator) {
		return combineInternal(other, combinator, new HashMap<>());
	}

	private <V2> Dawg<LETTER, V2> mapInternal(final Function<VALUE, V2> map,
			final Map<Dawg<LETTER, VALUE>, Dawg<LETTER, V2>> cache) {
		Dawg<LETTER, V2> result = cache.get(this);
		if (result != null) {
			return result;
		}
		if (mElseTransition == null) {
			result = createConst(0, map.apply(mFinal));
		} else {
			Dawg<LETTER, V2> elseCase = mElseTransition.mapInternal(map, cache);
			if (mTransitions.isEmpty()) {
				result = elseCase.createParent();
			} else {
				Map<LETTER, Dawg<LETTER, V2>> newTransitions = new LinkedHashMap<>();
				for (Map.Entry<LETTER, Dawg<LETTER, VALUE>> entry : mTransitions.entrySet()) {
					LETTER key = entry.getKey();
					Dawg<LETTER, V2> mapped = entry.getValue().mapInternal(map, cache);
					if (mapped != elseCase) {
						newTransitions.put(key, mapped);
					}
				}
				result = createDawg(newTransitions, elseCase);
			}
		}
		cache.put(this, result);
		return result;
	}

	/**
	 * Create a new dawg that uses the given map to map each value to a new value. This creates a dawg that maps each
	 * key to {@code map.apply(this.getValue(key))}.
	 * 
	 * @param map
	 *            the map function
	 * @return the mapped dawg.
	 */
	public <V2> Dawg<LETTER, V2> map(final Function<VALUE, V2> map) {
		return mapInternal(map, new HashMap<>());
	}

	private <V2> Dawg<LETTER, V2> mapWithKeyInternal(final BiFunction<List<LETTER>, VALUE, V2> map,
			final ArrayList<LETTER> key) {
		if (mElseTransition == null) {
			return createConst(0, map.apply(key, mFinal));
		} else {
			key.add(null);
			Dawg<LETTER, V2> elseCase = mElseTransition.mapWithKeyInternal(map, key);
			key.remove(key.size() - 1);
			if (mTransitions.isEmpty()) {
				return elseCase.createParent();
			} else {
				Map<LETTER, Dawg<LETTER, V2>> newTransitions = new LinkedHashMap<>();
				for (Map.Entry<LETTER, Dawg<LETTER, VALUE>> entry : mTransitions.entrySet()) {
					LETTER letter = entry.getKey();
					key.add(letter);
					Dawg<LETTER, V2> mapped = entry.getValue().mapWithKeyInternal(map, key);
					key.remove(key.size() - 1);
					if (mapped != elseCase) {
						newTransitions.put(letter, mapped);
					}
				}
				return createDawg(newTransitions, elseCase);
			}
		}
	}

	/**
	 * Create a new dawg that uses the given map to map each key/value pair to a new value. This creates a dawg that
	 * maps each key to {@code map.apply(key, this.getValue(key))}.
	 * 
	 * @param map
	 *            the map function
	 * @return the mapped dawg.
	 */
	public <V2> Dawg<LETTER, V2> mapWithKey(final BiFunction<List<LETTER>, VALUE, V2> map) {
		return mapWithKeyInternal(map, new ArrayList<>());
	}

	/**
	 * Create a new dawg that uses the given map to map each letter to a new letter. This is an internal function that
	 * works on a set of input dawgs. If the keys of two entries are mapped to the same new key, the union function is
	 * used to determine the new value. The union function is also used to combine the values from several input dawgs.
	 * 
	 * @param input
	 *            the set of input dawgs.
	 * @param map
	 *            the letter map.
	 * @param union
	 *            the union for values with keys that are mapped to identical keys.
	 * @return the mapped dawg.
	 */
	private static <LETTER, VALUE, LETTER2> Dawg<LETTER2, VALUE> mapKeysInternal(Set<Dawg<LETTER, VALUE>> input,
			final Function<LETTER, LETTER2> map, 
			final BiFunction<VALUE, VALUE, VALUE> union) {
		boolean isFinal = false;
		VALUE finalValue = null;
		// successors stores for each new key all old dawgs which are the successor of some old key in some
		// of the input dawgs where the old key is mapped to the new key.
		HashMap<LETTER2, HashSet<Dawg<LETTER, VALUE>>> successors = new LinkedHashMap<>();
		// elseSuccessors stores all else transitions of all input dawgs.
		HashSet<Dawg<LETTER, VALUE>> elseSuccessors = new LinkedHashSet<>();
		for (Dawg<LETTER, VALUE> inputDawg : input) {
			if (inputDawg.mElseTransition == null) {
				assert elseSuccessors.isEmpty() : "input set must not contain both final and non-final dawgs";
				isFinal = true;
				if (finalValue == null) {
					finalValue = inputDawg.getFinalValue();
				} else if (!finalValue.equals(inputDawg.getFinalValue())) {
					// union the finalValue, unless they are already equal.
					finalValue = union.apply(finalValue, inputDawg.getFinalValue());
				}
			} else {
				assert !isFinal : "input set must not contain both final and non-final dawgs";
				for (Map.Entry<LETTER, Dawg<LETTER, VALUE>> entry : inputDawg.mTransitions.entrySet()) {
					LETTER2 newKey = map.apply(entry.getKey());
					HashSet<Dawg<LETTER, VALUE>> succs = successors.get(newKey);
					if (succs == null) {
						succs = new LinkedHashSet<>();
						successors.put(newKey, succs);
					}
					succs.add(entry.getValue());
				}
				elseSuccessors.add(inputDawg.mElseTransition);
			}
		}
		if (isFinal) {
			// new final dawg.
			return createConst(0, finalValue);
		} else {
			// build new dawgs recursively by mapping the successors and elseSuccessors to new dawgs.
			HashMap<LETTER2, Dawg<LETTER2, VALUE>> newTransitions = new LinkedHashMap<>();
			for (Map.Entry<LETTER2, HashSet<Dawg<LETTER, VALUE>>> entry : successors.entrySet()) {
				newTransitions.put(entry.getKey(), mapKeysInternal(entry.getValue(), map, union));
			}
			return createDawg(newTransitions, mapKeysInternal(elseSuccessors, map, union));
		}
	}

	/**
	 * Create a new dawg that uses the given map to map each letter to a new letter. If the keys of two entries are
	 * mapped to the same new key, the union function is used to determine the new value.
	 * 
	 * @param map
	 *            the letter map
	 * @param union
	 *            the union for values with keys that are mapped to identical keys.
	 * @return the mapped dawg.
	 */
	public <LETTER2> Dawg<LETTER2, VALUE> mapKeys(final Function<LETTER, LETTER2> map,
			final BiFunction<VALUE, VALUE, VALUE> union) {
		return mapKeysInternal(Collections.singleton(this), map, union);
	}

	public boolean isFinal() {
		return mTransitions == null;
	}

	public VALUE getFinalValue() {
		return mFinal;
	}

	@Override
	public String toString() {
		if (isFinal()) {
			return "RET(" + mFinal + ")";
		}
		final StringBuilder sb = new StringBuilder();
		final LinkedHashSet<Dawg<LETTER, VALUE>> toPrint = new LinkedHashSet<>();
		final HashSet<Dawg<LETTER, VALUE>> visited = new HashSet<>();
		toPrint.add(this);
		while (!toPrint.isEmpty()) {
			final Dawg<LETTER, VALUE> state = toPrint.iterator().next();
			toPrint.remove(state);
			if (!visited.add(state)) {
				continue;
			}
			sb.append(String.format("Dawg#%04d", state.hashCode() % 10000));
			String comma ="";
			for (final Map.Entry<LETTER, Dawg<LETTER, VALUE>> entry : state.getTransitions().entrySet()) {
				sb.append(comma).append("->");
				if (entry.getValue().isFinal()) {
					sb.append("(").append(entry.getValue().getFinalValue()).append(") ");
				} else {
					sb.append(String.format("#%04d ", entry.getValue().hashCode() % 10000));
					toPrint.add(entry.getValue());
				}
				sb.append(entry.getKey());
				sb.append("\n");
				comma = "         ";
			}
			sb.append(comma).append("->");
			if (state.mElseTransition.isFinal()) {
				sb.append("(").append(state.mElseTransition.getFinalValue()).append(") ");
			} else {
				sb.append(String.format("#%04d ", state.mElseTransition.hashCode() % 10000));
				toPrint.add(state.mElseTransition);
			}
			sb.append("OTHERWISE\n");
		}
		return sb.toString();
	}

	/**
	 * Get the next step of the current Dawg, i.e., the goal of the transition with the given letter, or the goal of the
	 * elseTransition.
	 * 
	 * @return the next Dawg.
	 */
	public Dawg<LETTER, VALUE> getNextDawg(LETTER key) {
		Dawg<LETTER, VALUE> result = mTransitions.get(key);
		if (result == null) {
			result = mElseTransition;
		}
		return result;
	}

	public Map<LETTER, Dawg<LETTER, VALUE>> getTransitions() {
		return mTransitions;
	}

	public VALUE getValue(final List<LETTER> word) {
		Dawg<LETTER, VALUE> state = this;
		for (final LETTER letter : word) {
			assert !state.isFinal();
			state = state.getNextDawg(letter);
		}
		assert state.isFinal();
		return state.getFinalValue();
	}

	public Iterable<Entry<LETTER, VALUE>> entrySet() {
		if (isFinal()) {
			return Collections.singleton(new Entry<LETTER, VALUE>(Collections.emptyList(), this.mFinal));
		}
		return new Iterable<Entry<LETTER, VALUE>>() {
			@Override
			public Iterator<Entry<LETTER, VALUE>> iterator() {
				return new Iterator<Entry<LETTER, VALUE>>() {
					/**
					 * Iterator for all transitions. This is set to null, when we iterate the dawg for the
					 * elseTransition.
					 */
					Iterator<Map.Entry<LETTER, Dawg<LETTER, VALUE>>> mTransIterator = mTransitions.entrySet()
							.iterator();
					/**
					 * The entry currently iterated. If this is null, then we need to get the next entry from
					 * mTransIterator. This is an entry in the mTransitions hash map, or a special entry for the else
					 * transition with null key.
					 */
					Map.Entry<LETTER, Dawg<LETTER, VALUE>> mCurrentEntry = null;
					/**
					 * The iterator for the Dawg in mCurrentEntry.
					 */
					Iterator<Entry<LETTER, VALUE>> mSubIterator = null;

					@Override
					public boolean hasNext() {
						while (mSubIterator == null || !mSubIterator.hasNext()) {
							if (mTransIterator == null) {
								/* we iterated everything, even the default transition */
								return false;
							}
							if (mTransIterator.hasNext()) {
								mCurrentEntry = mTransIterator.next();
							} else {
								mTransIterator = null;
								mCurrentEntry = new Map.Entry<LETTER, Dawg<LETTER, VALUE>>() {
									@Override
									public LETTER getKey() {
										return null;
									}

									@Override
									public Dawg<LETTER, VALUE> getValue() {
										return mElseTransition;
									}

									@Override
									public Dawg<LETTER, VALUE> setValue(Dawg<LETTER, VALUE> value) {
										throw new UnsupportedOperationException();
									}
								};
							}
							mSubIterator = mCurrentEntry.getValue().entrySet().iterator();
						}
						return true;
					}

					@Override
					public Entry<LETTER, VALUE> next() {
						if (!hasNext()) {
							throw new NoSuchElementException();
						}
						assert mSubIterator != null && mSubIterator.hasNext();
						assert mCurrentEntry != null;
						final Entry<LETTER, VALUE> suffixEntry = mSubIterator.next();
						List<LETTER> newKey = new ConsList<LETTER>(mCurrentEntry.getKey(), suffixEntry.getKey());
						return new Dawg.Entry<>(newKey, suffixEntry.getValue());
					}
				};
			}
		};
	}

	public Iterable<VALUE> values() {
		if (isFinal()) {
			return Collections.singleton(this.mFinal);
		}
		return new Iterable<VALUE>() {
			private Set<Dawg<LETTER, VALUE>> mVisited = new HashSet<>();
			@Override
			public Iterator<VALUE> iterator() {
				return new Iterator<VALUE>() {
					/**
					 * Iterator for all transitions. This is set to null, when we iterate the dawg for the
					 * elseTransition.
					 */
					Iterator<Dawg<LETTER, VALUE>> mTransIterator =
							mTransitions.values().iterator();
					/**
					 * The entry currently iterated. If this is null, then we need to get the next entry from
					 * mTransIterator. This is an entry in the mTransitions hash map, or a special entry for the else
					 * transition with null key.
					 */
					Dawg<LETTER, VALUE> mCurrentEntry = null;
					/**
					 * The iterator for the Dawg in mCurrentEntry.
					 */
					Iterator<VALUE> mSubIterator = null;

					@Override
					public boolean hasNext() {
						while (mSubIterator == null || !mSubIterator.hasNext()) {
							if (mTransIterator == null) {
								/* we iterated everything, even the default transition */
								return false;
							}
							if (mTransIterator.hasNext()) {
								mCurrentEntry = mTransIterator.next();
							} else {
								mTransIterator = null;
								mCurrentEntry = mElseTransition;
							}
							if (mVisited.add(mCurrentEntry)) {
								mSubIterator = mCurrentEntry.values().iterator();
							} else {
								mSubIterator = null;
							}
						}
						return true;
					}

					@Override
					public VALUE next() {
						if (!hasNext()) {
							throw new NoSuchElementException();
						}
						assert mSubIterator != null && mSubIterator.hasNext();
						assert mCurrentEntry != null;
						return mSubIterator.next();
					}
				};
			}
		};
	}

	private static class ConsList<T> extends AbstractList<T> {
		private T mHead;
		private List<T> mTail;
		private int mSize;

		public ConsList(T head, List<T> tail) {
			mHead = head;
			mTail = tail;
			mSize = tail.size() + 1;
		}

		@Override
		public T get(int index) {
			return index == 0 ? mHead : mTail.get(index - 1);
		}

		@Override
		public int size() {
			return mSize;
		}
	}

	public static class Entry<LETTER, VALUE> {
		private List<LETTER> mKey;
		private VALUE mValue;

		public Entry(List<LETTER> key, VALUE value) {
			mKey = key;
			mValue = value;
		}

		public List<LETTER> getKey() {
			return mKey;
		}

		public VALUE getValue() {
			return mValue;
		}
	}

}
