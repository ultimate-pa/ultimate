package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateServiceProviderMock;

/** 
 * Operation of a treeAutomaton accepts a given Run.
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> letter of the tree automaton.
 * @param <STATE> state of the tree automaton.
 */
public class Accepts<LETTER, STATE> implements IOperation<LETTER, STATE> {
	private final TreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	private final Tree<LETTER> mExample;
	
	private final Boolean mResult;
	private final AutomataLibraryServices mServices;
	
	public Accepts(final AutomataLibraryServices services, final ITreeAutomatonBU<LETTER, STATE> automaton, 
			final TreeRun<LETTER, STATE> run) {
		this(services, automaton, run.getTree());
	}
	
	public Accepts(final AutomataLibraryServices services, final ITreeAutomatonBU<LETTER, STATE> automaton, 
			final Tree<LETTER> run) {
		mServices = services;
		mExample = run;
		mTreeAutomaton = (TreeAutomatonBU<LETTER, STATE>) automaton;
		
		mResult = computeResult();
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
		for (final Tree<LETTER> ch : t.getChildren()) {
			next.add(checkTree(ch));
		}
		
		final Iterable<TreeAutomatonRule<LETTER, STATE>> st = mTreeAutomaton.getRulesByLetter(t.getSymbol());
		
		if (st != null) {
			for (final TreeAutomatonRule<LETTER, STATE> rule : st) {
				if (rule.getSource().size() != next.size()) {
					continue;
				}
				for (int i = 0; i < next.size(); ++i) {
					final STATE sr = rule.getSource().get(i);
					if (!next.get(i).contains(sr) && !mTreeAutomaton.isInitialState(sr)) {
						continue;
					}
				}
				res.add(rule.getDest());
			}
		}
		return res;
	}

	private Boolean computeResult() {
		final Set<STATE> derivations = checkTree(mExample);
		for (final STATE st : derivations) {
			if (mTreeAutomaton.isFinalState(st)) {
				return true;
			}
		}
		return false;
	}
	@Override
	public Boolean getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO implement a meaningful check
		return true;
	}
	
	public static void main(String[] args) {
		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
		
		final String NAT = "NAT", NatList = "NatList", initA = "_";
		treeA.addInitialState(initA);
		treeA.addFinalState(NatList);
		treeA.addRule(new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[]{initA})), NAT));
		treeA.addRule(new TreeAutomatonRule<>("s", new ArrayList<>(Arrays.asList(new String[]{NAT})), NAT));
		treeA.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[]{initA})), NatList));
		treeA.addRule(new TreeAutomatonRule<>("cons", new ArrayList<>(Arrays.asList(new String[]{NAT, NatList})), NatList));
		
		// cons(0, cons(s(0), nil))
		final Tree<String> nil = new Tree<String>("nil");
		final Tree<String> zero1 = new Tree<String>("0");
		final Tree<String> zero2 = new Tree<String>("0");
		final ArrayList<Tree<String>> z1 = new ArrayList<Tree<String>>();
		z1.add(zero2);
		final Tree<String> one = new Tree<String>("s", z1);
		
		final ArrayList<Tree<String>> e2 = new ArrayList<>();
		e2.add(one);
		e2.add(nil);
		final Tree<String> elm2 = new Tree<String>("cons", e2);

		final ArrayList<Tree<String>> e1 = new ArrayList<>();
		e1.add(zero1);
		e1.add(elm2);
		final Tree<String> run = new Tree<String>("f", e1);
		
		final UltimateServiceProviderMock usp = new UltimateServiceProviderMock();
		final AutomataLibraryServices services = new AutomataLibraryServices(usp);
		
		final Accepts<String, String> op = new Accepts<>(services, treeA, run);
		
		System.out.println(run);
		System.out.println();
		System.out.println(op.getResult());
		
	}
}
