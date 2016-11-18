package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

public class Totalize<LETTER, STATE> implements IOperation<LETTER, STATE> {


	private final ITreeAutomaton<LETTER, STATE> treeAutomaton;
	private final IStateFactory<STATE> stateFactory;
	
	protected final ITreeAutomaton<LETTER, STATE> result;
	private final Map<Integer, List<List<STATE>>> memCombinations;
	
	private final STATE dummyState;
	private final Set<STATE> states;
	
	public Totalize(final ITreeAutomaton<LETTER, STATE> tree, final IStateFactory<STATE> factory) {
		treeAutomaton =  tree;
		stateFactory = factory;
		memCombinations = new HashMap<>();
		dummyState = stateFactory.createEmptyStackState();
		states = new HashSet<>();
		states.add(dummyState);
		states.addAll(tree.getStates());
		
		result = computeResult();
	}
	
	
	public List<List<STATE>> combinations(int siz) {
		if (memCombinations.containsKey(siz)) {
			return memCombinations.get(siz);
		}
		ArrayList<List<STATE>> res = new ArrayList<>();
		if (siz == 0) {
			ArrayList<STATE> st = new ArrayList<>();
			res.add(st);
			memCombinations.put(siz, res);
			return res;
		}
		List<List<STATE>> subres = combinations(siz - 1);
		for (final STATE st : states) {
			for (final List<STATE> subst : subres) {
				List<STATE> t = new ArrayList<>(subst.size());
				t.addAll(subst);
				t.add(st);
				res.add(t);
			}
		}
		memCombinations.put(siz, res);
		return res;
	}
	
	public TreeAutomatonBU<LETTER, STATE> computeResult() {
		final TreeAutomatonBU<LETTER, STATE> res = new TreeAutomatonBU<>();
		for (final STATE st : states) {
			res.addState(st);
			if (treeAutomaton.isFinalState(st)) {
				res.addFinalState(st);
			}
			if (treeAutomaton.isInitialState(st)) {
				res.addInitialState(st);
			}
		}
		
		for (final TreeAutomatonRule<LETTER, STATE> rule : treeAutomaton.getRules()) {
			res.addRule(rule);
			for (final List<STATE> srcSt : combinations(rule.getArity())) {
				Iterable<STATE> st = treeAutomaton.getSuccessors(srcSt, rule.getLetter());
				if (st != null && !st.iterator().hasNext()) {
					res.addRule(new TreeAutomatonRule<LETTER, STATE>(rule.getLetter(), srcSt, dummyState));
				}
			}
			
		}
		for (final LETTER sym : treeAutomaton.getAlphabet()) {
			Method getAr = null;
			int arity = -1;
			try {
				getAr = sym.getClass().getMethod("getArity");
			} catch (Exception e) {
				continue;
			}
			try {
				arity = (int) getAr.invoke(sym);
			} catch (Exception e) {
				continue;
			}
			if (arity >= 0) {
				//System.err.println(sym);
				for (final List<STATE> srcSt : combinations(arity)) {
					Iterable<STATE> st = treeAutomaton.getSuccessors(srcSt, sym);
					if (st != null && !st.iterator().hasNext()) {
						res.addRule(new TreeAutomatonRule<LETTER, STATE>(sym, srcSt, dummyState));
					}
				}
			}
		}
		return res;
	}
	@Override
	public String operationName() {
		return "Totalize";
	}

	@Override
	public String startMessage() {
		return "Starting " + operationName();
	}

	@Override
	public String exitMessage() {
		return "Finishing " + operationName();
	}

	@Override
	public ITreeAutomaton<LETTER, STATE> getResult() {
		return result;
	}

	@Override
	public boolean checkResult(IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
	
	public static void main(String[] args) {
		/*
		TreeAutomatonBU<Character, String> tree = new TreeAutomatonBU<>();
		tree.addFinalState("F");
		tree.addInitialState("T");
		
		ArrayList<String> src1 = new ArrayList<>();
		
		src1.add("T");
		tree.addRule(new TreeAutomatonRule<Character, String>('a', src1, "I"));

		ArrayList<String> src2 = new ArrayList<>();
		src2.add("I");
		tree.addRule(new TreeAutomatonRule<Character, String>('x', src2, "F"));
		
		Totalize<Character, String> op = new Totalize<>(tree, new StringFactory());
		System.out.println(tree);
		System.out.println(op.getResult());
		
		*/
		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
		
		final String NAT = "NAT", NatList = "NatList", initA = "_";
		treeA.addInitialState(initA);
		treeA.addFinalState(NatList);
		treeA.addRule("0", new ArrayList<>(Arrays.asList(new String[]{initA})), NAT);
		treeA.addRule("s", new ArrayList<>(Arrays.asList(new String[]{NAT})), NAT);
		treeA.addRule("nil", new ArrayList<>(Arrays.asList(new String[]{initA})), NatList);
		treeA.addRule("cons", new ArrayList<>(Arrays.asList(new String[]{NAT, NatList})), NatList);
		
		Totalize<String, String> op2 = new Totalize<>(treeA, new StringFactory());
		System.out.println(treeA);
		System.out.println(op2.getResult());
		
		
	}
}
