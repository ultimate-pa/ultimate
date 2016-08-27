package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

public class TreeEmptinessCheck<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final TreeAutomatonBU<LETTER, STATE> treeAutomaton;
	protected final Tree<LETTER> result;
	
	public TreeEmptinessCheck(final TreeAutomatonBU<LETTER, STATE> tree) {
		treeAutomaton = tree;
		result = computeResult();
	}
	@Override
	public String operationName() {
		return "Emptiness";
	}

	@Override
	public String startMessage() {
		return "Starting emptiness check";
	}

	@Override
	public String exitMessage() {
		return "Exit emptiness check";
	}
	private Tree<LETTER> computeResult() {
		final LinkedList<TreeAutomatonRule<LETTER, STATE>> worklist = new LinkedList<TreeAutomatonRule<LETTER, STATE>>();

		final Map<STATE, Collection<TreeAutomatonRule<LETTER, STATE>>> rulesBySource = new HashMap<STATE, Collection<TreeAutomatonRule<LETTER, STATE>>>();
		
		final Map<STATE, Tree<LETTER>> soltree = new HashMap<>();
		
		for (final TreeAutomatonRule<LETTER, STATE> rule: treeAutomaton.getRules()) {
			boolean initialRules = false;
			
			for (final STATE sourceState : rule.getSource()) {
				initialRules |= treeAutomaton.isInitialState(sourceState);
				
				Collection<TreeAutomatonRule<LETTER, STATE>> sourceRules;
				if (rulesBySource.containsKey(sourceState)) {
					sourceRules = rulesBySource.get(sourceState);
				} else {
					sourceRules = new LinkedList<TreeAutomatonRule<LETTER, STATE>>();
					rulesBySource.put(sourceState, sourceRules);
				}
				sourceRules.add(rule);
			}
			if (treeAutomaton.isInitialState(rule.getDest()) || initialRules) {
				worklist.add(rule);
			}
		}

		while (!worklist.isEmpty()) {
			final TreeAutomatonRule<LETTER, STATE> next = worklist.poll();
			final STATE dest = next.getDest();
			
			final List<Tree<LETTER>> subTrees = new LinkedList<Tree<LETTER>>();
			if (!soltree.containsKey(dest)) {
				
				boolean allMarked = true;
				for (final STATE q: next.getSource()) {
					if (!soltree.containsKey(q)) {
						allMarked = false;
						break;
					} else {
						subTrees.add(soltree.get(q));
					}
				}
				if (allMarked) {
					final Tree<LETTER> newTree = new Tree<LETTER>(next.getLetter(), subTrees);
					soltree.put(dest, newTree);
					
					if (treeAutomaton.isFinalState(dest)) {
						return newTree;
					} else {
						if (rulesBySource.containsKey(dest)) {
							for (final TreeAutomatonRule<LETTER, STATE> considerNext: rulesBySource.get(dest))
							 {
								worklist.add(considerNext);
								//worklist.push(considerNext); // depth first
							}
						}
					}
				}
			}
		}
		System.err.println(soltree);
		return null;
	}
	
	@Override
	public Object getResult() {
		return result;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return false;
	}

	public static void main(final String[] args) throws AutomataLibraryException {
		final TreeAutomatonBU<String, Integer> treeA = new TreeAutomatonBU<>();
		
		final String[] rep = {"Nat", "NatList", "Bool", "BoolList"};

		final int NAT = 0, NatList = 1, EmptyList = 2;
		treeA.addInitialState(NAT);
		treeA.addInitialState(EmptyList);
		treeA.addFinalState(NatList);
		treeA.addRule("0", new ArrayList<>(), NAT);
		treeA.addRule("s", new ArrayList<>(Arrays.asList(new Integer[]{NAT})), NAT);
		treeA.addRule("nil", new ArrayList<>(), EmptyList);
		treeA.addRule("cons", new ArrayList<>(Arrays.asList(new Integer[]{NAT, EmptyList})), NatList);
		treeA.addRule("cons", new ArrayList<>(Arrays.asList(new Integer[]{NAT, NatList})), NatList);

		final TreeEmptinessCheck<String, Integer> op = new TreeEmptinessCheck<>(treeA);
		final Tree<String> res = (Tree<String>) op.getResult();
		
		System.out.println(treeA.toString());
		System.out.println(res.toString());
	}
}
