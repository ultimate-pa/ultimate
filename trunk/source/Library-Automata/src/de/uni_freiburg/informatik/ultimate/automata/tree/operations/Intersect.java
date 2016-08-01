package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Intersect<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomaton<LETTER, STATE> treeA, treeB;
	
	protected final TreeAutomatonBU<LETTER, Pair<STATE, STATE>> res;
	
	private Map<STATE, Map<STATE, Pair<STATE, STATE>>> pairsMap;
	
	private Pair<STATE, STATE> getPair(STATE q1, STATE q2) {
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
	
	public Intersect(ITreeAutomaton<LETTER, STATE> t1, ITreeAutomaton<LETTER, STATE> t2) {
		treeA = t1;
		treeB = t2;
		
		res = computeResult();
	}
	@Override
	public String operationName() {
		return "Intersect";
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
		TreeAutomatonBU<LETTER, Pair<STATE, STATE>> res = new TreeAutomatonBU<>();
		
		Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> symbolToRuleA = new HashMap<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>>();
		Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> symbolToRuleB = new HashMap<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>>();
		
		for (TreeAutomatonRule<LETTER, STATE> ruleA : treeA.getRules()) {
			Collection<TreeAutomatonRule<LETTER, STATE>> rules;
			if (symbolToRuleA.containsKey(ruleA.getLetter())) {
				rules = symbolToRuleA.get(ruleA.getLetter());
			} else {
				rules = new LinkedList<TreeAutomatonRule<LETTER, STATE>>();
				symbolToRuleA.put(ruleA.getLetter(), rules);
			}
			rules.add(ruleA);
		}
		for (TreeAutomatonRule<LETTER, STATE> ruleB : treeB.getRules()) {
			Collection<TreeAutomatonRule<LETTER, STATE>> rules;
			if (symbolToRuleB.containsKey(ruleB.getLetter())) {
				rules = symbolToRuleB.get(ruleB.getLetter());
			} else {
				rules = new LinkedList<TreeAutomatonRule<LETTER, STATE>>();
				symbolToRuleB.put(ruleB.getLetter(), rules);
			}
			rules.add(ruleB);
		}
		
		for (LETTER letter : symbolToRuleA.keySet()) {
			if (symbolToRuleB.containsKey(letter)) {
				for (TreeAutomatonRule<LETTER, STATE> ruleA : symbolToRuleA.get(letter)) {
					for (TreeAutomatonRule<LETTER, STATE> ruleB : symbolToRuleB.get(letter)) {
						if (ruleA.getArity() == ruleB.getArity()) {
							List<Pair<STATE, STATE>> source = new ArrayList<>();
							int ar = ruleA.getArity();
							for (int i = 0; i < ar; ++i) {
								source.add(getPair(ruleA.getSource().get(i), ruleB.getSource().get(i)));
							}
							Pair<STATE, STATE> dest = getPair(ruleA.getDest(), ruleB.getDest());
							res.addRule(letter, source, dest);
						}
					}
				}
			}
		}
		if (pairsMap == null) {
			pairsMap = new HashMap<>();
		}
		for (STATE q1 : pairsMap.keySet()) {
			for (STATE q2 : pairsMap.get(q1).keySet()) {
				Pair<STATE, STATE> st = getPair(q1, q2);
				
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
	public Object getResult() throws AutomataLibraryException {
		return res;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
	
	public static void main(String[] args) throws AutomataLibraryException {
		TreeAutomatonBU<String, Integer> treeA = new TreeAutomatonBU<>();
		TreeAutomatonBU<String, Integer> treeB = new TreeAutomatonBU<>();
		
		final int NAT = 0, NatList = 1, Bool = 2, BoolList = 3;
		String[] rep = {"Nat", "NatList", "Bool", "BoolList"};
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
		
		Intersect<String, Integer> op = new Intersect<>(treeA, treeB);
		TreeAutomatonBU<String, Integer> res = (TreeAutomatonBU<String, Integer>) op.getResult();
		
		System.out.println(treeA.toString() + "\n");
		System.out.println(treeB.toString() + "\n");
		System.out.println(res.toString() + "\n");
	}
}
