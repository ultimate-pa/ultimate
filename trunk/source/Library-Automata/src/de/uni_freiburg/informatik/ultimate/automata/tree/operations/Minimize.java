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
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

/**
 * Minimize a given treeAutomaton.
 * 
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 *
 * @param <LETTER>
 *            letter of the tree automaton.
 * @param <STATE>
 *            state of the tree automaton.
 */
public class Minimize<LETTER extends IRankedLetter, STATE> implements IOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final TreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	private final IMergeStateFactory<STATE> mStateFactory;
	
	protected final ITreeAutomatonBU<LETTER, STATE> mResult;

	private final Map<Set<STATE>, STATE> mMinimizedStates;

	/***
	 * Constructor of Minimize operator
	 * @param services
	 * @param factory
	 * @param tree
	 */
	public Minimize(final AutomataLibraryServices services, final IMergeStateFactory<STATE> factory,
			final ITreeAutomatonBU<LETTER, STATE> tree) {
		mTreeAutomaton = (TreeAutomatonBU<LETTER, STATE>) tree;
		mStateFactory = factory;
		mMinimizedStates = new HashMap<>();
		mResult = computeResult();
	}

	private STATE minimize(final Set<STATE> st) {
		// minimize set of state to a new minimized state.
		if (!mMinimizedStates.containsKey(st)) {
			mMinimizedStates.put(st, mStateFactory.merge(st));
		}
		return mMinimizedStates.get(st);
	}

	@Override
	public String startMessage() {
		return "Starting " + getOperationName();
	}

	@Override
	public String exitMessage() {
		return "Exiting " + getOperationName();
	}

	/***
	 * Check if 2 states are replacable (equivalent)
	 * @param s1
	 * @param s2
	 * @param rule
	 * @param worklist
	 * @return
	 */
	private boolean replacable(final STATE s1, final STATE s2, final TreeAutomatonRule<LETTER, STATE> rule,
			final DisjointSet<STATE> worklist) {
		final ArrayList<STATE> src = new ArrayList<>();
		for (final STATE st : rule.getSource()) {
			src.add(st);
		}
		for (int idx = 0; idx < src.size(); ++idx) {
			if (src.get(idx) != s1) {
				continue;
			}
			final ArrayList<STATE> s = (ArrayList<STATE>) src.clone();
			s.set(idx, s2);
			// If we replace an occurance of s1 by s2 in the rule, and it still yields an equivalent destination
			// Then we can replace s2 by s1 in this rule
			// TODO(amin): Check if just one occurance or all of them is needed.
			for (final STATE dest : mTreeAutomaton.getSuccessors(s, rule.getLetter())) {
				if (worklist.equiv(dest, rule.getDest())) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean replacable(final STATE s1, final STATE s2, final DisjointSet<STATE> partitions) {
		// If I can replace s1 by s2 in all rules of s1
		for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getRulesBySource(s1)) {
			if (!replacable(s1, s2, rule, partitions)) {
				return false;
			}
		}

		// If I can replace s2 by s1 in all rules of s2
		for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getRulesBySource(s2)) {
			if (!replacable(s2, s1, rule, partitions)) {
				return false;
			}
		}
		// Then both states are equivalent hence replacable.
		return true;
	}

	private ITreeAutomatonBU<LETTER, STATE> computeResult() {
		//return removeUnreachables(mTreeAutomaton);
		
		DisjointSet<STATE> worklist = new DisjointSet<>(mTreeAutomaton.getStates());
		STATE finalState = null;
		STATE initState = null;
		STATE nonFinalState = null;
		for (final STATE state : mTreeAutomaton.getStates()) {
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
		DisjointSet<STATE> oldWorklist;
		do {
			oldWorklist = worklist;

			worklist = new DisjointSet<>(mTreeAutomaton.getStates());
			for (final Iterator<Set<STATE>> partitionsIt = oldWorklist.getParitionsIterator(); partitionsIt
					.hasNext();) {
				final Set<STATE> partition = partitionsIt.next();
				final ArrayList<STATE> states = new ArrayList<>();
				for (final Iterator<STATE> it = partition.iterator(); it.hasNext();) {
					states.add(it.next());
				}
				for (int i = 0; i < states.size(); ++i) {
					final STATE p1 = states.get(i);
					for (int j = 0; j < i; ++j) {
						// for each pair of states
						final STATE p2 = states.get(j);
						// if we can replace p1 and p2 together
						if (!oldWorklist.equiv(p1, p2) && replacable(p1, p2, oldWorklist)) {
							// then mark as equivalent
							worklist.union(p1, p2);
						}
					}
				}
			}
		} while (!worklist.equals(oldWorklist));

		// minimize all states
		final TreeAutomatonBU<LETTER, STATE> res = new TreeAutomatonBU<>();
		for (final STATE st : mTreeAutomaton.getStates()) {
			res.addState(minimize(worklist.getPartition(st)));
			if (mTreeAutomaton.isFinalState(st)) {
				res.addFinalState(minimize(worklist.getPartition(st)));
			}
			if (mTreeAutomaton.isInitialState(st)) {
				res.addInitialState(minimize(worklist.getPartition(st)));
			}
		}

		for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getRules()) {
			final List<STATE> src = new ArrayList<>();
			// minimize all set of states in all rules.
			for (final STATE st : rule.getSource()) {
				src.add(minimize(worklist.getPartition(st)));
			}
			res.addRule(
					new TreeAutomatonRule<>(rule.getLetter(), src, minimize(worklist.getPartition(rule.getDest()))));
		}
		return removeUnreachables(res);
		
	}

	private ITreeAutomatonBU<LETTER, STATE> removeUnreachables(final TreeAutomatonBU<LETTER, STATE> treeAutomaton) {
		final TreeAutomatonBU<LETTER, STATE> res = new TreeAutomatonBU<>();

		final Set<STATE> worklist = new HashSet<>();

		for (final STATE st : treeAutomaton.getInitialStates()) {
			worklist.add(st);
		}
		final Set<STATE> oldWorklist = new HashSet<>();

		do {
			oldWorklist.addAll(worklist);

			for (final TreeAutomatonRule<LETTER, STATE> rule : treeAutomaton.getRules()) {
				// If the sources of this rule are reachable, then is the destination.
				boolean allFound = true;
				for (final STATE sr : rule.getSource()) {
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

		final Set<STATE> visited = new HashSet<>();
		// All reachable nodes from initial states.
		visited.addAll(worklist);

		worklist.clear();
		oldWorklist.clear();
		for (final STATE st : visited) {
			if (treeAutomaton.isFinalState(st)) {
				// needed final states.
				worklist.add(st);
			}
		}

		do {
			oldWorklist.addAll(worklist);

			for (final STATE dest : oldWorklist) {
				// for each needed state mark all it's predecessors as needed.
				final Map<LETTER, Iterable<List<STATE>>> prev = treeAutomaton.getPredecessors(dest);
				for (final LETTER symb : prev.keySet()) {
					for (final List<STATE> src : prev.get(symb)) {
						boolean allFound = true;
						for (final STATE st : src) {
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

		for (final STATE st : worklist) {
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
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
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

		@Override
		public boolean equals(final Object set) {
			// TODO: Did you possibly want to override equals here? You did not, and I made that explicit by renaming
			// this method to equalsTo
			if (!(set instanceof DisjointSet)) {
				return false;
			}
			final DisjointSet<T> other = (DisjointSet<T>) set;
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
