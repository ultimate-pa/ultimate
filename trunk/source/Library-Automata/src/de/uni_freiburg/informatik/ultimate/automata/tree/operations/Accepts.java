package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;

/** 
 * Operation of a treeAutomaton accepts a given Run.
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> letter of the tree automaton.
 * @param <STATE> state of the tree automaton.
 */
public class Accepts<LETTER, STATE> implements IOperation<LETTER, STATE> {
	private final TreeAutomatonBU<LETTER, STATE> treeAutomaton;
	private final Tree<LETTER> example;
	
	private final Boolean result;
	
	public Accepts(final ITreeAutomaton<LETTER, STATE> automaton, final TreeRun<LETTER, STATE> run) {
		this(automaton, run.getTree());
	}
	
	public Accepts(final ITreeAutomaton<LETTER, STATE> automaton, final Tree<LETTER> run) {
		example = run;
		treeAutomaton = (TreeAutomatonBU<LETTER, STATE>) automaton;
		
		result = computeResult();
	}
	@Override
	public String operationName() {
		return "TreeAccepts";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName();
	}

	@Override
	public String exitMessage() {
		return "Exit " + operationName();
	}
	
	private Set<STATE> checkTree(final Tree<LETTER> t) {
		final Set<STATE> res = new HashSet<>();
		
		final ArrayList<Set<STATE>> next = new ArrayList<>();
		for (Tree<LETTER> ch : t.getChildren()) {
			next.add(checkTree(ch));
		}
		
		final Iterable<TreeAutomatonRule<LETTER, STATE>> st = treeAutomaton.getRulesByLetter(t.getSymbol());
		
		if (st != null) {
			for (final TreeAutomatonRule<LETTER, STATE> rule : st) {
				if (rule.getSource().size() != next.size()) {
					continue;
				}
				for (int i = 0; i < next.size(); ++i) {
					final STATE sr = rule.getSource().get(i);
					if (!next.get(i).contains(sr) && !treeAutomaton.isInitialState(sr)) {
						continue;
					}
				}
				res.add(rule.getDest());
			}
		}
		return res;
	}

	private Boolean computeResult() {
		final Set<STATE> derivations = checkTree(example);
		for (final STATE st : derivations) {
			if (treeAutomaton.isFinalState(st)) {
				return true;
			}
		}
		return false;
	}
	@Override
	public Boolean getResult() {
		return result;
	}

	@Override
	public boolean checkResult(IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
	
	public static void main(String[] args) {
		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
		
		final String NAT = "NAT", NatList = "NatList", initA = "_";
		treeA.addInitialState(initA);
		treeA.addFinalState(NatList);
		treeA.addRule("0", new ArrayList<>(Arrays.asList(new String[]{initA})), NAT);
		treeA.addRule("s", new ArrayList<>(Arrays.asList(new String[]{NAT})), NAT);
		treeA.addRule("nil", new ArrayList<>(Arrays.asList(new String[]{initA})), NatList);
		treeA.addRule("cons", new ArrayList<>(Arrays.asList(new String[]{NAT, NatList})), NatList);
		
		// cons(0, cons(s(0), nil))
		Tree<String> nil = new Tree<String>("nil");
		Tree<String> zero1 = new Tree<String>("0");
		Tree<String> zero2 = new Tree<String>("0");
		ArrayList<Tree<String>> z1 = new ArrayList<Tree<String>>();
		z1.add(zero2);
		Tree<String> one = new Tree<String>("s", z1);
		
		ArrayList<Tree<String>> e2 = new ArrayList<>();
		e2.add(one);
		e2.add(nil);
		Tree<String> elm2 = new Tree<String>("cons", e2);

		ArrayList<Tree<String>> e1 = new ArrayList<>();
		e1.add(zero1);
		e1.add(elm2);
		Tree<String> run = new Tree<String>("f", e1);
		
		final Accepts<String, String> op = new Accepts<>(treeA, run);
		
		System.out.println(run);
		System.out.println();
		System.out.println(op.getResult());
		
	}
}
