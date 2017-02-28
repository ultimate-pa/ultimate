/*
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2014-2016 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

/**
 * Minimize a given treeAutomaton.
 * 
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 *
 * @param <R>
 *            letter of the tree automaton.
 * @param <S>
 *            state of the tree automaton.
 */
public class Minimize<R, S> implements IOperation<R, S, IStateFactory<S>> {

	private final TreeAutomatonBU<R, S> mTreeAutomaton;
	private final IMergeStateFactory<S> mStateFactory;
	
	protected final ITreeAutomatonBU<R, S> mResult;

	private final Map<Set<S>, S> mMinimizedStates;

	/***
	 * Constructor of Minimize operator
	 * @param services
	 * @param factory
	 * @param tree
	 */
	public Minimize(final AutomataLibraryServices services, final IMergeStateFactory<S> factory,
			final ITreeAutomatonBU<R, S> tree) {
		mTreeAutomaton = (TreeAutomatonBU<R, S>) tree;
		mStateFactory = factory;
		mMinimizedStates = new HashMap<>();
		mResult = computeResult();
	}

	private S minimize(final Set<S> st) {
		// minimize set of state to a new minimized state.
		if (!mMinimizedStates.containsKey(st)) {
			mMinimizedStates.put(st, mStateFactory.merge(st));
		}
		return mMinimizedStates.get(st);
	}

	@Override
	public String operationName() {
		return "Minimize";
	}

	@Override
	public String startMessage() {
		return "Starting " + operationName();
	}

	@Override
	public String exitMessage() {
		return "Exiting " + operationName();
	}

	/***
	 * Check if 2 states are replacable (equivalent)
	 * @param s1
	 * @param s2
	 * @param rule
	 * @param worklist
	 * @return
	 */
	private boolean replacable(final S s1, final S s2, final TreeAutomatonRule<R, S> rule,
			final DisjointSet<S> worklist) {
		final ArrayList<S> src = new ArrayList<>();
		for (final S st : rule.getSource()) {
			src.add(st);
		}
		for (int idx = 0; idx < src.size(); ++idx) {
			if (src.get(idx) != s1) {
				continue;
			}
			final ArrayList<S> s = (ArrayList<S>) src.clone();
			s.set(idx, s2);
			// If we replace an occurance of s1 by s2 in the rule, and it still yields an equivalent destination
			// Then we can replace s2 by s1 in this rule
			// TODO(amin): Check if just one occurance or all of them is needed.
			for (final S dest : mTreeAutomaton.getSuccessors(s, rule.getLetter())) {
				if (worklist.equiv(dest, rule.getDest())) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean replacable(final S s1, final S s2, final DisjointSet<S> partitions) {
		// If I can replace s1 by s2 in all rules of s1
		for (final TreeAutomatonRule<R, S> rule : mTreeAutomaton.getRulesBySource(s1)) {
			if (!replacable(s1, s2, rule, partitions)) {
				return false;
			}
		}

		// If I can replace s2 by s1 in all rules of s2
		for (final TreeAutomatonRule<R, S> rule : mTreeAutomaton.getRulesBySource(s2)) {
			if (!replacable(s2, s1, rule, partitions)) {
				return false;
			}
		}
		// Then both states are equivalent hence replacable.
		return true;
	}

	private ITreeAutomatonBU<R, S> computeResult() {

		DisjointSet<S> worklist = new DisjointSet<>(mTreeAutomaton.getStates());
		S finalState = null;
		S initState = null;
		S nonFinalState = null;
		for (final S state : mTreeAutomaton.getStates()) {
			if (mTreeAutomaton.isFinalState(state)) {
				if (finalState == null) {
					finalState = state;
				} else {
					// All final states are equivalent.
					worklist.union(finalState, state);
				}
			} else if (mTreeAutomaton.isInitialState(state)) {
				if (initState == null) {
					initState = state;
				} else {
					// all initial states are equivalent
					worklist.union(initState, state);
				}
			} else {
				if (nonFinalState == null) {
					nonFinalState = state;
				} else {
					worklist.union(nonFinalState, state);
				}
			}
		}
		DisjointSet<S> oldWorklist;
		do {
			oldWorklist = worklist;

			worklist = new DisjointSet<>(mTreeAutomaton.getStates());
			for (final Iterator<Set<S>> partitionsIt = oldWorklist.getParitionsIterator(); partitionsIt
					.hasNext();) {
				final Set<S> partition = partitionsIt.next();
				final ArrayList<S> states = new ArrayList<>();
				for (final Iterator<S> it = partition.iterator(); it.hasNext();) {
					states.add(it.next());
				}
				for (int i = 0; i < states.size(); ++i) {
					final S p1 = states.get(i);
					for (int j = 0; j < i; ++j) {
						// for each pair of states
						final S p2 = states.get(j);
						// if we can replace p1 and p2 together
						if (!oldWorklist.equiv(p1, p2) && replacable(p1, p2, oldWorklist)) {
							// then mark as equivalent
							worklist.union(p1, p2);
						}
					}
				}
			}
		} while (!worklist.equalsTo(oldWorklist));

		// minimize all states
		final TreeAutomatonBU<R, S> res = new TreeAutomatonBU<>();
		for (final S st : mTreeAutomaton.getStates()) {
			res.addState(minimize(worklist.getPartition(st)));
			if (mTreeAutomaton.isFinalState(st)) {
				res.addFinalState(minimize(worklist.getPartition(st)));
			}
			if (mTreeAutomaton.isInitialState(st)) {
				res.addInitialState(minimize(worklist.getPartition(st)));
			}
		}

		for (final TreeAutomatonRule<R, S> rule : mTreeAutomaton.getRules()) {
			final List<S> src = new ArrayList<>();
			// minimize all set of states in all rules.
			for (final S st : rule.getSource()) {
				src.add(minimize(worklist.getPartition(st)));
			}
			res.addRule(
					new TreeAutomatonRule<>(rule.getLetter(), src, minimize(worklist.getPartition(rule.getDest()))));
		}
		return removeUnreachables(res);
	}

	private ITreeAutomatonBU<R, S> removeUnreachables(final TreeAutomatonBU<R, S> treeAutomaton) {
		final TreeAutomatonBU<R, S> res = new TreeAutomatonBU<>();

		final Set<S> worklist = new HashSet<>();

		for (final S st : treeAutomaton.getInitialStates()) {
			worklist.add(st);
		}
		final Set<S> oldWorklist = new HashSet<>();

		do {
			oldWorklist.addAll(worklist);

			for (final TreeAutomatonRule<R, S> rule : treeAutomaton.getRules()) {
				// If the sources of this rule are reachable, then is the destination.
				boolean allFound = true;
				for (final S sr : rule.getSource()) {
					if (!oldWorklist.contains(sr)) {
						allFound = false;
						break;
					}
				}
				if (allFound) {
					worklist.add(rule.getDest());
				}
			}
			// no new reachable states
		} while (!worklist.equals(oldWorklist));

		final Set<S> visited = new HashSet<>();
		// All reachable nodes from initial states.
		visited.addAll(worklist);

		worklist.clear();
		oldWorklist.clear();
		for (final S st : visited) {
			if (treeAutomaton.isFinalState(st)) {
				// needed final states.
				worklist.add(st);
			}
		}

		do {
			oldWorklist.addAll(worklist);

			for (final S dest : oldWorklist) {
				// for each needed state mark all it's predecessors as needed.
				final Map<R, Iterable<List<S>>> prev = treeAutomaton.getPredecessors(dest);
				for (final R symb : prev.keySet()) {
					for (final List<S> src : prev.get(symb)) {
						boolean allFound = true;
						for (final S st : src) {
							// If a final state has a never-reachable predecessor, then this is an invalid rule.
							if (!visited.contains(st)) {
								allFound = false;
								break;
							}
						}
						if (allFound) {
							// Reachable Rule, Needed State
							res.addRule(new TreeAutomatonRule<>(symb, src, dest));
							// all source states are needed.
							worklist.addAll(src);
						}
					}
				}
			}
		} while (!worklist.equals(oldWorklist));

		for (final S st : worklist) {
			if (visited.contains(st)) {
				res.addState(st);
				if (treeAutomaton.isFinalState(st)) {
					res.addFinalState(st);
				}
				if (treeAutomaton.isInitialState(st)) {
					res.addInitialState(st);
				}
			}
		}

		return res;
	}

	@Override
	public ITreeAutomatonBU<R, S> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<S> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}

	/***
	 * DisjointSets data structure.
	 * @author Mostafa M.A. <mostafa.amin93@gmail.com>
	 *
	 * @param <T> Elements of the sets
	 */
	protected static class DisjointSet<T> {
		private final Map<T, T> mRepr;
		private final Map<T, Set<T>> mSubsets;

		public DisjointSet(final Set<T> elements) {
			mRepr = new HashMap<>();
			mSubsets = new HashMap<>();
			for (final T x : elements) {
				mRepr.put(x, x);
				final Set<T> sub = new HashSet<>();
				sub.add(x);
				mSubsets.put(x, sub);
			}
		}

		@Override
		public String toString() {
			final StringBuilder res = new StringBuilder("Rep:");
			for (final Entry<T, T> s : mRepr.entrySet()) {
				res.append(" " + s.getKey() + "in" + s.getValue());
			}
			res.append("\nPart:");
			for (final Entry<T, Set<T>> s : mSubsets.entrySet()) {
				res.append(" " + s.getKey() + "in" + mSubsets.get(s.getValue()));
			}
			return res.toString();
		}

		/***
		 * Size of the disjoint set.
		 * @return
		 */
		public int size() {
			int siz = 0;
			for (final Set<T> subset : mSubsets.values()) {
				if (!subset.isEmpty()) {
					++siz;
				}
			}
			return siz;
		}

		private T changeRep(final T x, final T rNew) {
			final T rOld = mRepr.get(x);
			if (rOld == rNew) {
				return rNew;
			}
			mRepr.put(x, rNew);
			if (mSubsets.containsKey(rOld)) {
				mSubsets.get(rOld).remove(x);
			}
			mSubsets.get(rNew).add(x);
			return rNew;
		}

		/***
		 * Union of the two disjoint sets.
		 * @param x
		 * @param y
		 */
		public void union(final T x, final T y) {
			changeRep(y, find(x));
		}

		/***
		 * Find the representative of the corresponding disjoint set.
		 * @param x
		 * @return
		 */
		public T find(final T x) {
			final T res = mRepr.get(x);
			if (res == x) {
				return res;
			}
			return changeRep(x, find(res));
		}

		/***
		 * Check if two elements are equivalent by checking if the disjoint sets are the same.
		 * @param x
		 * @param y
		 * @return
		 */
		public boolean equiv(final T x, final T y) {
			return find(x) == find(y);
		}

		Set<T> getPartition(final T x) {
			return mSubsets.get(find(x));
		}

		private void findAll(final T x) {
			for (final T y : mSubsets.get(x)) {
				if (y != x) {
					findAll(y);
				}
			}
			find(x);
		}

		public boolean equalsTo(final DisjointSet<T> other) {
			// TODO: Did you possibly want to override equals here? You did not, and I made that explicit by renaming
			// this method to equalsTo
			if (other == null) {
				return false;
			}
			if (!other.mRepr.keySet().equals(mRepr.keySet())) {
				// Not same elements
				return false;
			}
			for (final T x : other.mRepr.keySet()) {
				// the partition of every element, is not the same partition in the other disjointset
				if (!other.mSubsets.get(other.mRepr.get(x)).equals(mSubsets.get(mRepr.get(x)))) {
					return false;
				}
			}
			return true;
		}

		public Iterator<Set<T>> getParitionsIterator() {
			final Iterator<T> it = mSubsets.keySet().iterator();

			return new Iterator<Set<T>>() {
				T mCur = null;

				public boolean keepMoving() {
					if (!it.hasNext()) {
						mCur = null;
						return false;
					}
					do {
						mCur = it.next();
						findAll(mCur);
					} while (it.hasNext() && mSubsets.get(mCur).isEmpty());
					if (mSubsets.get(mCur).isEmpty()) {
						mCur = null;
						return false;
					}
					return true;
				}

				@Override
				public boolean hasNext() {
					if (mCur == null) {
						return keepMoving();
					}
					return true;
				}

				@Override
				public Set<T> next() {
					if (hasNext()) {
						final Set<T> res = mSubsets.get(mCur);
						keepMoving();
						return res;
					}
					throw new NoSuchElementException("No more elments to iterate.");
				}
			};
		}
	}
}
