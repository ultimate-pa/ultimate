package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateServiceProviderMock;

/**
 *  Complements a given treeAutomaton.
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> letter of the tree automaton.
 * @param <STATE> state of the tree automaton.
 */
public class Complement<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	private final IMergeStateFactory<STATE> mStateFactory;
	
	protected final ITreeAutomatonBU<LETTER, STATE> mResult;
	private final AutomataLibraryServices mServices;
	
	public Complement(final AutomataLibraryServices services, final IMergeStateFactory<STATE> factory, 
			final ITreeAutomatonBU<LETTER, STATE> tree) {
		mServices = services;
		mTreeAutomaton = tree;
		mStateFactory = factory;
		
		mResult = computeResult();
	}
	@Override
	public String operationName() {
		return "Complement";
	}

	@Override
	public String startMessage() {
		return "Starting complementing";
	}

	@Override
	public String exitMessage() {
		return "Exiting complementing";
	}
	
	private ITreeAutomatonBU<LETTER, STATE> computeResult() {
		final Determinize<LETTER, STATE> op = new Determinize<>(mServices, mStateFactory, mTreeAutomaton);
		final TreeAutomatonBU<LETTER, STATE> res = (TreeAutomatonBU<LETTER, STATE>) op.getResult();
		res.complementFinals();
		final Minimize<LETTER, STATE> mini = new Minimize<>(mServices, mStateFactory, res);
		return mini.getResult();
	}
	
	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO implement a meaningful check
		return true;
	}
	
	public static void main(final String[] args) throws AutomataLibraryException {
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

		final UltimateServiceProviderMock usp = new UltimateServiceProviderMock();
		final AutomataLibraryServices services = new AutomataLibraryServices(usp);

		final StringFactory fac = new StringFactory();
		final Complement<String, String> com = new Complement<>(services, fac, treeB);
		
		final Intersect<String, String> op = new Intersect<>(services, fac, treeA, com.getResult());
		final ITreeAutomatonBU<String, String> res = op.getResult();
		
		System.out.println(treeA.toString() + "\n");
		System.out.println(treeB.toString() + "\n");
		System.out.println(com.getResult() + "\n");
		System.out.println(res + "\n");
		System.out.println(((TreeAutomatonBU<String, String>) res).DebugString() + "\n");
	}
}
