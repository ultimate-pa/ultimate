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
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Intersect<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomaton<LETTER, STATE> treeA, treeB;
	
	protected final TreeAutomatonBU<LETTER, Pair<STATE, STATE>> res;
	
	private Map<STATE, Map<STATE, Pair<STATE, STATE>>> pairsMap;
	
	private Pair<STATE, STATE> getPair(final STATE q1, final STATE q2) {
		if (pairsMap == null) {
			pairsMap = new HashMap<>();
		}
		if (!pairsMap.containsKey(q1)) {
			pairsMap.put(q1, new HashMap<>());
		}
		if (!pairsMap.get(q1).containsKey(q2)) {
			pairsMap.get(q1).put(q2, new Pair<STATE, STATE>(q1, q2));
		}
		return pairsMap.get(q1).get(q2);
	}
	
	public Intersect(final ITreeAutomaton<LETTER, STATE> t1, final ITreeAutomaton<LETTER, STATE> t2) {
		treeA = t1;
		treeB = t2;
		
		res = computeResult();
	}
	@Override
	public String operationName() {
		return "ta_intersect";
	}

	@Override
	public String startMessage() {
		return "Start intersection tree automatons";
	}

	@Override
	public String exitMessage() {
		return "Exit intersection tree automatons";
	}
	
	private TreeAutomatonBU<LETTER, Pair<STATE, STATE>> computeResult() {
		// Minimal states intersection.
		final TreeAutomatonBU<LETTER, Pair<STATE, STATE>> res = new TreeAutomatonBU<>();
		
		final Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> symbolToRuleA = new HashMap<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>>();
		final Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> symbolToRuleB = new HashMap<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>>();
		
		for (final TreeAutomatonRule<LETTER, STATE> ruleA : treeA.getRules()) {
			Collection<TreeAutomatonRule<LETTER, STATE>> rules;
			if (symbolToRuleA.containsKey(ruleA.getLetter())) {
				rules = symbolToRuleA.get(ruleA.getLetter());
			} else {
				rules = new LinkedList<TreeAutomatonRule<LETTER, STATE>>();
				symbolToRuleA.put(ruleA.getLetter(), rules);
			}
			rules.add(ruleA);
		}
		for (final TreeAutomatonRule<LETTER, STATE> ruleB : treeB.getRules()) {
			Collection<TreeAutomatonRule<LETTER, STATE>> rules;
			if (symbolToRuleB.containsKey(ruleB.getLetter())) {
				rules = symbolToRuleB.get(ruleB.getLetter());
			} else {
				rules = new LinkedList<TreeAutomatonRule<LETTER, STATE>>();
				symbolToRuleB.put(ruleB.getLetter(), rules);
			}
			rules.add(ruleB);
		}
		
		for (final LETTER letter : symbolToRuleA.keySet()) {
			if (symbolToRuleB.containsKey(letter)) {
				for (final TreeAutomatonRule<LETTER, STATE> ruleA : symbolToRuleA.get(letter)) {
					for (final TreeAutomatonRule<LETTER, STATE> ruleB : symbolToRuleB.get(letter)) {
						if (ruleA.getArity() == ruleB.getArity()) {
							final List<Pair<STATE, STATE>> source = new ArrayList<>();
							final int ar = ruleA.getArity();
							for (int i = 0; i < ar; ++i) {
								source.add(getPair(ruleA.getSource().get(i), ruleB.getSource().get(i)));
							}
							final Pair<STATE, STATE> dest = getPair(ruleA.getDest(), ruleB.getDest());
							res.addRule(letter, source, dest);
						}
					}
				}
			}
		}
		if (pairsMap == null) {
			pairsMap = new HashMap<>();
		}
		for (final STATE q1 : pairsMap.keySet()) {
			for (final STATE q2 : pairsMap.get(q1).keySet()) {
				final Pair<STATE, STATE> st = getPair(q1, q2);
				
				if (treeA.isInitialState(q1) && treeB.isInitialState(q2)) {
					res.addInitialState(st);
				}

				if (treeA.isFinalState(q1) && treeB.isFinalState(q2)) {
					res.addFinalState(st);
				}
			}
		}
		
		return res;
	}
	@Override
	public TreeAutomatonBU getResult() {
		return res;
	}

	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
	
	public static void main(final String[] args) throws AutomataLibraryException {
		final TreeAutomatonBU<String, Integer> treeA = new TreeAutomatonBU<>();
		final TreeAutomatonBU<String, Integer> treeB = new TreeAutomatonBU<>();
		
		final int NAT = 0, NatList = 1, Bool = 2, BoolList = 3;
		final String[] rep = {"Nat", "NatList", "Bool", "BoolList"};
		treeA.addInitialState(NAT);
		treeA.addFinalState(NatList);
		treeA.addRule("0", new ArrayList<>(), NAT);
		treeA.addRule("s", new ArrayList<>(Arrays.asList(new Integer[]{NAT})), NAT);
		treeA.addRule("nil", new ArrayList<>(), NatList);
		treeA.addRule("cons", new ArrayList<>(Arrays.asList(new Integer[]{NAT, NatList})), NatList);
		
		treeB.addInitialState(Bool);
		treeB.addFinalState(BoolList);
		treeB.addRule("0", new ArrayList<>(), Bool);
		treeB.addRule("1", new ArrayList<>(), Bool);
		treeB.addRule("nil", new ArrayList<>(), BoolList);
		treeB.addRule("cons", new ArrayList<>(Arrays.asList(new Integer[]{Bool, BoolList})), BoolList);
		
		final Intersect<String, Integer> op = new Intersect<>(treeA, treeB);
		final TreeAutomatonBU<String, Integer> res = op.getResult();
		
		System.out.println(treeA.toString() + "\n");
		System.out.println(treeB.toString() + "\n");
		System.out.println(res.toString() + "\n");
	}
}
