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
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
/**
 * Check emptiness of a tree automaton. The output is TreeRun.
 * @author mostafa
 *
 * @param <LETTER> letter class of tree automaton.
 * @param <STATE> state class of tree automaton.
 */
public class TreeEmptinessCheck<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomaton<LETTER, STATE> treeAutomaton;
	protected final TreeRun<LETTER, STATE> result;
	
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
	
	private TreeRun<LETTER, STATE> computeResult() {
		final LinkedList<TreeAutomatonRule<LETTER, STATE>> worklist = new LinkedList<>();

		final Map<STATE, Collection<TreeAutomatonRule<LETTER, STATE>>> rulesBySource = new HashMap<>();
		
		final Map<STATE, TreeRun<LETTER, STATE>> soltree = new HashMap<>();
		
		for (final STATE init : treeAutomaton.getInitialStates()) {
			soltree.put(init, new TreeRun<LETTER, STATE>(init));
		}
		for (final TreeAutomatonRule<LETTER, STATE> rule: treeAutomaton.getRules()) {
			boolean initialRules = true;
			
			for (final STATE sourceState : rule.getSource()) {
				initialRules &= treeAutomaton.isInitialState(sourceState);
				
				Collection<TreeAutomatonRule<LETTER, STATE>> sourceRules;
				if (rulesBySource.containsKey(sourceState)) {
					sourceRules = rulesBySource.get(sourceState);
				} else {
					sourceRules = new LinkedList<>();
					rulesBySource.put(sourceState, sourceRules);
				}
				sourceRules.add(rule);
			}
			if (initialRules) {
				worklist.add(rule);
			}
		}

		while (!worklist.isEmpty()) {
			final TreeAutomatonRule<LETTER, STATE> rule = worklist.poll();
			final STATE dest = rule.getDest();
			
			final List<TreeRun<LETTER, STATE>> subTrees = new LinkedList<>();
			if (soltree.containsKey(dest)) {
				// Already computed.
				continue;
			}
				
			boolean allMarked = true;
			for (final STATE q: rule.getSource()) {
				if (!soltree.containsKey(q)) {
					allMarked = false;
					break;
				} else {
					subTrees.add(soltree.get(q));
				}
			}
			if (allMarked) {
				final TreeRun<LETTER, STATE> newTree = new TreeRun<LETTER, STATE>(dest, rule.getLetter(), subTrees);
				soltree.put(dest, newTree);
				
				if (treeAutomaton.isFinalState(dest)) {
					return newTree;
				} else {
					if (rulesBySource.containsKey(dest)) {
						for (final TreeAutomatonRule<LETTER, STATE> considerNext: rulesBySource.get(dest)) {
							worklist.add(considerNext);
							//worklist.push(considerNext); // depth first
						}
					}
				}
			}
		
		}
		return null;
	}
	
	@Override
	public TreeRun<LETTER, STATE> getResult() {
		return result;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return false;
	}

	public static void main(String[] args) throws AutomataLibraryException {
		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
		
		final String NAT = "N", NatList = "L", EmptyList = "EL", init = "_";
		
		treeA.addInitialState(init);
		treeA.addFinalState(NatList);
		treeA.addRule("0", new ArrayList<>(Arrays.asList(new String[]{init})), NAT);
		treeA.addRule("s", new ArrayList<>(Arrays.asList(new String[]{NAT})), NAT);
		treeA.addRule("nil", new ArrayList<>(Arrays.asList(new String[]{init})), EmptyList);
		treeA.addRule("cons", new ArrayList<>(Arrays.asList(new String[]{NAT, EmptyList})), NatList);
		treeA.addRule("cons", new ArrayList<>(Arrays.asList(new String[]{NAT, NatList})), NatList);

		final TreeEmptinessCheck<String, String> op = new TreeEmptinessCheck<>(treeA);
		final TreeRun<String, String> res = op.getResult();
		
		System.out.println(treeA.toString());
		System.out.println();
		System.out.println(res.toString());
		System.out.println();
		System.out.println(res.getTree().toString());
		System.out.println();
		System.out.println(res.getAutomaton().toString());
	}
}
