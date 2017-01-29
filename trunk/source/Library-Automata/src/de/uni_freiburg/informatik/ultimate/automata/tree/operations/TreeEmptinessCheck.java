package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateServiceProviderMock;
/**
 * Check emptiness of a tree automaton. The output is TreeRun.
 * @author mostafa
 *
 * @param <LETTER> letter class of tree automaton.
 * @param <STATE> state class of tree automaton.
 */
public class TreeEmptinessCheck<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	protected final TreeRun<LETTER, STATE> mResult;
	private AutomataLibraryServices mServices;
	
	public TreeEmptinessCheck(final AutomataLibraryServices services, final TreeAutomatonBU<LETTER, STATE> tree) {
		mServices = services;
		mTreeAutomaton = tree;
		mResult = computeResult();
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
		
		for (final STATE init : mTreeAutomaton.getInitialStates()) {
			soltree.put(init, new TreeRun<LETTER, STATE>(init));
		}
		for (final TreeAutomatonRule<LETTER, STATE> rule: mTreeAutomaton.getRules()) {
			boolean initialRules = true;
			
			for (final STATE sourceState : rule.getSource()) {
				initialRules &= mTreeAutomaton.isInitialState(sourceState);
				
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
				
				if (mTreeAutomaton.isFinalState(dest)) {
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
		return mResult;
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
		treeA.addRule(new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[]{init})), NAT));
		treeA.addRule(new TreeAutomatonRule<>("s", new ArrayList<>(Arrays.asList(new String[]{NAT})), NAT));
		treeA.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[]{init})), EmptyList));
		treeA.addRule(new TreeAutomatonRule<>("cons", new ArrayList<>(Arrays.asList(new String[]{NAT, EmptyList})), NatList));
		treeA.addRule(new TreeAutomatonRule<>("cons", new ArrayList<>(Arrays.asList(new String[]{NAT, NatList})), NatList));

		final UltimateServiceProviderMock usp = new UltimateServiceProviderMock();
		final AutomataLibraryServices services = new AutomataLibraryServices(usp);

		final TreeEmptinessCheck<String, String> op = new TreeEmptinessCheck<>(services, treeA);
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
