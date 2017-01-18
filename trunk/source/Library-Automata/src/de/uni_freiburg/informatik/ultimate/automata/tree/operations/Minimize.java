package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

/**
 * Minimize a given treeAutomaton.
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> letter of the tree automaton.
 * @param <STATE> state of the tree automaton.
 */
public class Minimize<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final TreeAutomatonBU<LETTER, STATE> treeAutomaton;
	private final IStateFactory<STATE> stateFactory;
	
	protected final ITreeAutomatonBU<LETTER, STATE> result;

	final Map<Set<STATE>, STATE> minimizedStates;
	
	public Minimize(final ITreeAutomatonBU<LETTER, STATE> tree, final IStateFactory<STATE> factory) {
		treeAutomaton = (TreeAutomatonBU<LETTER, STATE>) tree;
		stateFactory = factory;
		minimizedStates = new HashMap<>();
		
		result = computeResult();
	}

	private STATE minimize(final Set<STATE> st) {
		if (!minimizedStates.containsKey(st)) {
			minimizedStates.put(st, stateFactory.minimize(st));
		}
		return minimizedStates.get(st);
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

	private boolean replacable(final STATE s1, final STATE s2,
			final TreeAutomatonRule<LETTER, STATE> rule, final DisjointSet<STATE> worklist) {
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
			for (final STATE dest : treeAutomaton.getSuccessors(s, rule.getLetter())) {
				if (worklist.equiv(dest, rule.getDest())) {
					return true;
				}
			}
		}
		return false;
	}
	private boolean replacable(final STATE s1, final STATE s2, final DisjointSet<STATE> partitions) {
		for (final TreeAutomatonRule<LETTER, STATE> rule : treeAutomaton.getRulesBySource(s1)) {
			if (!replacable(s1, s2, rule, partitions)) {
				return false;
			}
		}
		for (final TreeAutomatonRule<LETTER, STATE> rule : treeAutomaton.getRulesBySource(s2)) {
			if (!replacable(s2, s1, rule, partitions)) {
				return false;
			}
		}
		return true;
	}
	
	private ITreeAutomatonBU<LETTER, STATE> computeResult() {
		

		DisjointSet<STATE> worklist = new DisjointSet<>(treeAutomaton.getStates());
		STATE finalState = null;
		STATE initState = null;
		STATE nonFinalState = null;
		for (final STATE state : treeAutomaton.getStates()) {
			if (treeAutomaton.isFinalState(state)) {
				if (finalState == null) {
					finalState = state;
				} else {
					worklist.union(finalState, state);
				}
			} else if (treeAutomaton.isInitialState(state)) {
				if (initState == null) {
					initState = state;
				} else {
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
			//System.err.println(worklist.subsets);
			oldWorklist = worklist;

			worklist = new DisjointSet<>(treeAutomaton.getStates());
			for (Iterator<Set<STATE>> partitionsIt = oldWorklist.getParitionsIterator(); partitionsIt.hasNext();) {
				final Set<STATE> partition = partitionsIt.next();
				for (final Iterator<STATE> it1 = partition.iterator(); it1.hasNext();) {
					final STATE p1 = it1.next();
					for (final Iterator<STATE> it2 = partition.iterator(); it2.hasNext();) {
						final STATE p2 = it2.next();
						if (p1 == p2) {
							break;
						}
						if (replacable(p1, p2, oldWorklist)) {
							worklist.union(p1, p2);
						}
					}
				}
			}
		} while (!worklist.equals(oldWorklist));
		
		final TreeAutomatonBU<LETTER, STATE> res = new TreeAutomatonBU<>();
		for (final STATE st : treeAutomaton.getStates()) {
			res.addState(minimize(worklist.getPartition(st)));
			if (treeAutomaton.isFinalState(st)) {
				res.addFinalState(minimize(worklist.getPartition(st)));
			}
			if (treeAutomaton.isInitialState(st)) {
				res.addInitialState(minimize(worklist.getPartition(st)));
			}
		}
		
		for (final TreeAutomatonRule<LETTER, STATE> rule : treeAutomaton.getRules()) {
			final List<STATE> src = new ArrayList<>();
			for (final STATE st : rule.getSource()) {
				src.add(minimize(worklist.getPartition(st)));
			}
			res.addRule(new TreeAutomatonRule<LETTER, STATE>(rule.getLetter(), src, minimize(worklist.getPartition(rule.getDest()))));
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
			
		} while (!worklist.equals(oldWorklist));
		
		final Set<STATE> visited = new HashSet<>();
		visited.addAll(worklist);
		
		worklist.clear();
		oldWorklist.clear();
		for (final STATE st : visited) {
			if (treeAutomaton.isFinalState(st)) {
				worklist.add(st);
			}
		}
		
		do {
			oldWorklist.addAll(worklist);
			
			for (final STATE dest : oldWorklist) {
				final Map<LETTER, Iterable<List<STATE>>> prev = treeAutomaton.getPredecessors(dest);
				for (final LETTER symb : prev.keySet()) {
					for (final List<STATE> src : prev.get(symb)) {
						boolean allFound = true;
						for (final STATE st : src) {
							if (!visited.contains(st)) {
								allFound = false;
								break;
							}
						}
						if (allFound) {
							// Reachable Rule, Needed State
							res.addRule(symb, src, dest);
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
		return result;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
	
	public static void main(String[] args) throws AutomataLibraryException {
		HashSet<Integer> x = new HashSet<>();
		for (int i = 0; i < 15; ++i) {
			x.add(i + 1);
		}
		DisjointSet<Integer> st = new DisjointSet<>(x);

		for (int i = 1; i < 15; i += 2) {
			st.union(i, i + 2);
		}
		st.union(3, 1);
		for (Iterator<Set<Integer>> it = st.getParitionsIterator(); it.hasNext();) {
			System.out.println(it.next());
		}
		for (int i = 1; i <= 15; ++i) {
			System.out.println(i + " " + st.find(i));
		}
		for (int i = 1; i <= 15; ++i) {
			System.out.println(i + " " + st.getPartition(i));
		}
		
		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
		final String init = "_", X = "X", Y = "Y";
		treeA.addInitialState(init);
		treeA.addFinalState(Y);
		treeA.addRule("I", new ArrayList<>(Arrays.asList(new String[]{init})), X);
		treeA.addRule("I", new ArrayList<>(Arrays.asList(new String[]{init})), Y);
		treeA.addRule("F", new ArrayList<>(Arrays.asList(new String[]{X})), X);
		treeA.addRule("F", new ArrayList<>(Arrays.asList(new String[]{X})), Y);
		treeA.addRule("F", new ArrayList<>(Arrays.asList(new String[]{Y})), Y);
		
		System.out.println(treeA.toString() + "\n");
		final Determinize<String, String> det = new Determinize<>(treeA, new StringFactory());
		System.out.println(det.getResult());
		final Minimize<String, String> op = new Minimize<>(det.getResult(), new StringFactory());
		System.out.println(op.getResult());
		
	}
	
	protected static class DisjointSet<T> {
		private final Map<T, T> repr;
		private final Map<T, Set<T>> subsets;
		
		public DisjointSet(final Set<T> elements) {
			repr = new HashMap<>();
			subsets = new HashMap<>();
			for (final T x : elements) {
				repr.put(x, x);
				Set<T> sub = new HashSet<>();
				sub.add(x);
				subsets.put(x, sub);
			}
		}
		
		private T changeRep(final T x, final T rNew) {
			final T rOld = repr.get(x);
			if (rOld == rNew) {
				return rNew;
			}
			repr.put(x, rNew);
			if (subsets.containsKey(rOld)) {
				subsets.get(rOld).remove(x);
			}
			subsets.get(rNew).add(x);
			return rNew;
		}
		
		public void union(final T x, final T y) {
			changeRep(y, find(x));
		}
		
		public T find(final T x) {
			final T res = repr.get(x);
			if (res == x) {
				return res;
			}
			return changeRep(x, find(res));
		}
		
		public boolean equiv(final T x, final T y) {
			return find(x) == find(y);
		}
		
		private Set<T> getPartition(final T x) {
			return subsets.get(find(x));
		}
		
		private void findAll(final T x) {
			for (final T y : subsets.get(x)) {
				if (y != x) {
					findAll(y);
				}
			}
			find(x);
		}
		
		public boolean equals(final DisjointSet<T> S) {
			if (!S.repr.keySet().equals(repr.keySet()) || !S.subsets.keySet().equals(subsets.keySet())) {
				return false;
			}
			for (final T x : S.repr.keySet()) {
				if (!S.repr.get(x).equals(repr.get(x))) {
					return false;
				}
				if (!S.subsets.get(x).equals(subsets.get(x))) {
					
				}
			}
			return true;
		}
		public Iterator<Set<T>> getParitionsIterator() {
			final Iterator<T> it = subsets.keySet().iterator();
			
			return new Iterator<Set<T>>() {
				T cur = null;
				
				public boolean keepMoving() {
					if (!it.hasNext()) {
						cur = null;
						return false;
					}
					do {
						cur = it.next();
						findAll(cur);
					} while (it.hasNext() && subsets.get(cur).isEmpty());
					if (subsets.get(cur).isEmpty()) {
						cur = null;
						return false;
					}
					return true;
				}
				@Override
				public boolean hasNext() {
					if (cur == null) {
						return keepMoving();
					}
					return true;
				}

				@Override
				public Set<T> next() {
					if (hasNext()) {
						final Set<T> res = subsets.get(cur);
						keepMoving();
						return res;
					}
					return null;
				}
			};
		}
	}
}
