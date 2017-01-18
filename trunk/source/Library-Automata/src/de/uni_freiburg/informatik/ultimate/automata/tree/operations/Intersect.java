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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Intersect 2 tree automatons. 
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> letter of the tree automatons.
 * @param <STATE> state of the tree automatons.
 */
public class Intersect<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	private final ITreeAutomatonBU<LETTER, STATE> treeA;
	private final ITreeAutomatonBU<LETTER, STATE> treeB;
	protected final ITreeAutomatonBU<LETTER, STATE> result;
	
	private final IStateFactory<STATE> stateFactory;
	private final Map<STATE, Map<STATE, Pair<STATE, STATE>>> pairsMap;
	private final Map<Pair<STATE, STATE>, STATE> reducedStates;

	/**
	 * 
	 * NOTE: because of a convention in TestFileInterpreter, if an argument for the operation is a StateFactory, it must be the first argument
	 * same for Services, both: first services then StateFactory
	 * @param factory
	 * @param t1
	 * @param t2
	 */
	public Intersect(final IStateFactory<STATE> factory, final ITreeAutomatonBU<LETTER, STATE> t1, final ITreeAutomatonBU<LETTER, STATE> t2) {
		reducedStates = new HashMap<>();
		pairsMap = new HashMap<>();
		
		stateFactory = factory;
		treeA = t1;
		treeB = t2;
		result = computeResult();
	}
	
	private STATE reduceState(final Pair<STATE, STATE> key) {
		if (!reducedStates.containsKey(key)) {
			reducedStates.put(key, stateFactory.intersection(key.getFirst(), key.getSecond()));
		}
		return reducedStates.get(key);
	}
	
	private Pair<STATE, STATE> getPair(final STATE q1, final STATE q2) {
		if (!pairsMap.containsKey(q1)) {
			pairsMap.put(q1, new HashMap<>());
		}
		if (!pairsMap.get(q1).containsKey(q2)) {
			pairsMap.get(q1).put(q2, new Pair<STATE, STATE>(q1, q2));
		}
		return pairsMap.get(q1).get(q2);
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
	
	private TreeAutomatonBU<LETTER, STATE> computeResult() {
		// Minimal states intersection.
		final TreeAutomatonBU<LETTER, Pair<STATE, STATE>> res = new TreeAutomatonBU<>();
		
		final Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> symbolToRuleA = new HashMap<>();
		final Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> symbolToRuleB = new HashMap<>();
		
		for (final TreeAutomatonRule<LETTER, STATE> ruleA : treeA.getRules()) {
			Collection<TreeAutomatonRule<LETTER, STATE>> rules;
			if (symbolToRuleA.containsKey(ruleA.getLetter())) {
				rules = symbolToRuleA.get(ruleA.getLetter());
			} else {
				rules = new LinkedList<>();
				symbolToRuleA.put(ruleA.getLetter(), rules);
			}
			rules.add(ruleA);
		}
		for (final TreeAutomatonRule<LETTER, STATE> ruleB : treeB.getRules()) {
			Collection<TreeAutomatonRule<LETTER, STATE>> rules;
			if (symbolToRuleB.containsKey(ruleB.getLetter())) {
				rules = symbolToRuleB.get(ruleB.getLetter());
			} else {
				rules = new LinkedList<>();
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
							res.addRule(new TreeAutomatonRule<>(letter, source, dest));
						}
					}
				}
			}
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
		
		final TreeAutomatonBU<LETTER, STATE> reducedResult = new TreeAutomatonBU<>();
		
		for (final TreeAutomatonRule<LETTER, Pair<STATE, STATE>> rule : res.getRules()) {
			final List<STATE> src = new ArrayList<>();
			for (final Pair<STATE, STATE> pr : rule.getSource()) {
				src.add(reduceState(pr));
			}
			reducedResult.addRule(new TreeAutomatonRule<>(rule.getLetter(), src, reduceState(rule.getDest())));
		}
		
		for (final Pair<STATE, STATE> state : res.getStates()) {
			reducedResult.addState(reduceState(state));
			if (res.isInitialState(state)) {
				reducedResult.addInitialState(reduceState(state));
			}
			if (res.isFinalState(state)) {
				reducedResult.addFinalState(reduceState(state));
			}
		}
		
		return reducedResult;
	}
	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return result;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO: implement a meaningful check
		return true;
	}
	
	public static void main(String[] args) throws AutomataLibraryException {
		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
		final TreeAutomatonBU<String, String> treeB = new TreeAutomatonBU<>();
		
		final String NAT = "NAT", NatList = "NatList", Bool = "Bool", BoolList = "BoolList", initA = "_", initB = "_";
		treeA.addInitialState(initA);
		treeA.addFinalState(NatList);
		treeA.addRule(new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[]{initA})), NAT));
		treeA.addRule(new TreeAutomatonRule<>("s", new ArrayList<>(Arrays.asList(new String[]{NAT})), NAT));
		treeA.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[]{initA})), NatList));
		treeA.addRule(new TreeAutomatonRule<>("cons", new ArrayList<>(Arrays.asList(new String[]{NAT, NatList})), NatList));
		
		treeB.addInitialState(initB);
		treeB.addFinalState(BoolList);
		treeB.addRule(new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[]{initB})), Bool));
		treeB.addRule(new TreeAutomatonRule<>("1", new ArrayList<>(Arrays.asList(new String[]{initB})), Bool));
		treeB.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[]{initB})), BoolList));
		treeB.addRule(new TreeAutomatonRule<>("cons", new ArrayList<>(Arrays.asList(new String[]{Bool, BoolList})), BoolList));

		final StringFactory fac = new StringFactory();
		final Intersect<String, String> op = new Intersect<>(fac, treeA, treeB);
		final ITreeAutomatonBU<String, String> res = op.getResult();
		
		System.out.println(treeA.toString() + "\n");
		System.out.println(treeB.toString() + "\n");
		System.out.println(res + "\n");
		System.out.println(((TreeAutomatonBU<String, String>) res).DebugString() + "\n");
		
		final TreeAutomatonBU<Character, String> tree1 = new TreeAutomatonBU<>();
		final String I = "I", T = "T", F = "F", E = "E";
		tree1.addRule(new TreeAutomatonRule<>('A', new ArrayList<>(Arrays.asList(new String[]{T})), I));
		tree1.addRule(new TreeAutomatonRule<>('B', new ArrayList<>(Arrays.asList(new String[]{I})), I));
		tree1.addRule(new TreeAutomatonRule<>('C', new ArrayList<>(Arrays.asList(new String[]{I})), F));
		tree1.addFinalState(F);
		tree1.addInitialState(T);
		
		final TreeAutomatonBU<Character, String> tree2 = new TreeAutomatonBU<>();
		tree2.addRule(new TreeAutomatonRule<>('A', new ArrayList<>(Arrays.asList(new String[]{T})), I));
		tree2.addRule(new TreeAutomatonRule<>('B', new ArrayList<>(Arrays.asList(new String[]{T})), E));
		tree2.addRule(new TreeAutomatonRule<>('C', new ArrayList<>(Arrays.asList(new String[]{T})), E));
		
		tree2.addRule(new TreeAutomatonRule<>('A', new ArrayList<>(Arrays.asList(new String[]{I})), E));
		tree2.addRule(new TreeAutomatonRule<>('B', new ArrayList<>(Arrays.asList(new String[]{I})), E));
		tree2.addRule(new TreeAutomatonRule<>('C', new ArrayList<>(Arrays.asList(new String[]{I})), F));
		
		tree2.addRule(new TreeAutomatonRule<>('A', new ArrayList<>(Arrays.asList(new String[]{F})), E));
		tree2.addRule(new TreeAutomatonRule<>('B', new ArrayList<>(Arrays.asList(new String[]{F})), E));
		tree2.addRule(new TreeAutomatonRule<>('C', new ArrayList<>(Arrays.asList(new String[]{F})), E));

		tree2.addRule(new TreeAutomatonRule<>('A', new ArrayList<>(Arrays.asList(new String[]{E})), E));
		tree2.addRule(new TreeAutomatonRule<>('B', new ArrayList<>(Arrays.asList(new String[]{E})), E));
		tree2.addRule(new TreeAutomatonRule<>('C', new ArrayList<>(Arrays.asList(new String[]{E})), E));
		tree2.addInitialState(T);
		tree2.addFinalState(I);
		tree2.addFinalState(T);
		tree2.addFinalState(E);
		
		System.out.println(tree1);
		System.out.println(tree2);
		final Intersect<Character, String> oo = new Intersect<>(fac, tree1, tree2);
		final Minimize<Character, String> oo2 = new Minimize<>(fac, oo.getResult());
		System.out.println(oo2.getResult());
	}
}
