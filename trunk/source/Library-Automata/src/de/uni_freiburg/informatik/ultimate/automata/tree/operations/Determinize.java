package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

public class Determinize<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomaton<LETTER, STATE> tree;

	protected final ITreeAutomaton<LETTER, Set<STATE>> res;
	
	
	public Determinize(final ITreeAutomaton<LETTER, STATE> tree) {
		this.tree = tree;
		this.res = computeResult();
	}
	
	@Override
	public String operationName() {
		return "Determinization";
	}

	@Override
	public String startMessage() {
		return "Starting determinization";
	}

	@Override
	public String exitMessage() {
		return "Exiting determinization";
	}
	
	private TreeAutomatonBU<LETTER, Set<STATE>> computeResult() {
		final TreeAutomatonBU<LETTER, Set<STATE>> res = new TreeAutomatonBU<>();
		final Map<STATE, Set<STATE>> stateToSState = new HashMap<>();
		
		final Map<LETTER, Map<List<Set<STATE>>, Set<STATE>>> rules = new HashMap<LETTER, Map<List<Set<STATE>>, Set<STATE>>>();
		
		for (final TreeAutomatonRule<LETTER, STATE> rule : tree.getRules()) {
			if (!rules.containsKey(rule.getLetter())) {
				rules.put(rule.getLetter(), new HashMap<>());
			}
			final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(rule.getLetter());
			final List<Set<STATE>> source = new ArrayList<>();
			for (final STATE sr : rule.getSource()) {
				if (!stateToSState.containsKey(sr)) {
					final Set<STATE> nw = new HashSet<>();
					nw.add(sr);
					stateToSState.put(sr, nw);
				}
				source.add(stateToSState.get(sr));
			}
			final STATE sr = rule.getDest();
			if (!stateToSState.containsKey(sr)) {
				final Set<STATE> nw = new HashSet<>();
				nw.add(sr);
				stateToSState.put(sr, nw);
			}
			if (!mp.containsKey(source)) {
				mp.put(source, new HashSet<STATE>());
			}
			mp.get(source).add(sr);
		}
		
		final LinkedList<Set<STATE>> worklist = new LinkedList<>();
		for (final LETTER letter : rules.keySet()) {
			final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(letter);
			for (final List<Set<STATE>> st : mp.keySet()) {
				if (mp.get(st).size() > 1) {
					worklist.add(mp.get(st));
				}
			}
		}
		System.err.println(worklist);
		final Set<Set<STATE>> visited = new HashSet<Set<STATE>>();
		while (!worklist.isEmpty()) {
			final Set<STATE> state = worklist.poll();
			System.err.println(state);
			if (visited.contains(state))  {
				continue;
			}
			visited.add(state);
			final Map<LETTER, Map<List<Set<STATE>>, Set<Set<STATE>>>> newRules = new HashMap<LETTER, Map<List<Set<STATE>>, Set<Set<STATE>>>>();
			for (final LETTER letter : rules.keySet()) {
				if (!newRules.containsKey(letter)) {
					newRules.put(letter, new HashMap<>());
				}
				final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(letter);
				for (final List<Set<STATE>> key : mp.keySet()) {
					final ArrayList<Set<STATE>> src = (ArrayList<Set<STATE>>) key;
					final Set<STATE> dest = mp.get(key);
					// letter(src) -> dest
					int idx = 0;
					for (final Set<STATE> srcQ : src) {
						if (state.containsAll(srcQ)) {
							final ArrayList<Set<STATE>> toAdd = (ArrayList<Set<STATE>>) src.clone();
							toAdd.set(idx, state);
							
							if (!newRules.get(letter).containsKey(toAdd)) {
								newRules.get(letter).put(toAdd, new HashSet<Set<STATE>>());
							}
							//System.err.println(letter + " " + toAdd + " ~~> " + dest) ;
							newRules.get(letter).get(toAdd).add(dest);
						}
						++idx;
					}
				}
			}
			for (final LETTER letter : newRules.keySet()) {
				final Map<List<Set<STATE>>, Set<Set<STATE>>> mp = newRules.get(letter);
				for (final List<Set<STATE>> st : mp.keySet()) {
				
					final Set<STATE> uni = new HashSet<STATE>();
					for (final Set<STATE> s : mp.get(st)) {
						uni.addAll(s);
					}
					rules.get(letter).put(st, uni);
					if (mp.get(st).size() > 1) {
						worklist.add(uni);
					}
				}
			}
		}
		for (final LETTER letter : rules.keySet()) {
			final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(letter);
			for (final List<Set<STATE>> st : mp.keySet()) {
				final Set<STATE> dest = mp.get(st);
				res.addRule(letter, st, dest);
				
				for (final Set<STATE> e : st) {
					for (final STATE s : e) {
						if (tree.isInitialState(s)) {
							res.addInitialState(e);
						}
						if (tree.isFinalState(s)) {
							// TODO: should be redundant
							res.addFinalState(e);
						}
					}
				}
				for (final STATE s : dest) {
					if (tree.isFinalState(s)) {
						res.addFinalState(dest);
					}
					if (tree.isInitialState(s)) {
						// TODO: should be redundant
						res.addInitialState(dest);
					}
				}
			}
		}
		return res;
	}
	@Override
	public Object getResult() {
		return res;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return false;
	}


	public static void main(final String[] args) throws AutomataLibraryException {
		final TreeAutomatonBU<String, Integer> treeA = new TreeAutomatonBU<>();
		
		final int Q0 = 0, Q1 = 1, Q2 = 2, Q3 = 3;
		treeA.addInitialState(Q0);
		treeA.addFinalState(Q3);
		treeA.addRule("F", new ArrayList<>(Arrays.asList(new Integer[]{Q0, Q1})), Q2);
		treeA.addRule("F", new ArrayList<>(Arrays.asList(new Integer[]{Q0, Q1})), Q3);
		treeA.addRule("G", new ArrayList<>(Arrays.asList(new Integer[]{Q2})), Q3);
		treeA.addRule("G", new ArrayList<>(Arrays.asList(new Integer[]{Q3})), Q3);
		treeA.addRule("H", new ArrayList<>(Arrays.asList(new Integer[]{Q0, Q2})), Q1);
		treeA.addRule("H", new ArrayList<>(Arrays.asList(new Integer[]{Q0, Q3})), Q1);
		
		final Determinize<String, Integer> op = new Determinize<>(treeA);
		final TreeAutomatonBU<String, Set<Integer>> res = (TreeAutomatonBU<String, Set<Integer>>) op.getResult();
		
		System.out.println(treeA.toString() + "\n");
		System.out.println(res.toString() + "\n");
	}
}
