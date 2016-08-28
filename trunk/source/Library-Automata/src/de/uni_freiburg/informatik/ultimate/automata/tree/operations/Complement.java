package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;

public class Complement<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomaton<LETTER, STATE> treeAutomaton;
	protected final ITreeAutomaton<LETTER, STATE> result;
	
	private final StateFactory<STATE> stateFactory;
	
	public Complement(final ITreeAutomaton<LETTER, STATE> tree, StateFactory<STATE> factory) {
		treeAutomaton = tree;
		stateFactory = factory;
		
		result = computeResult();
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
	
	private ITreeAutomaton<LETTER, STATE> computeResult() {
		final Determinize<LETTER, STATE> op = new Determinize<LETTER, STATE>(treeAutomaton, stateFactory);
		final TreeAutomatonBU<LETTER, STATE> res = (TreeAutomatonBU<LETTER, STATE>) op.getResult();
		res.complementFinals();
		
		return res;
	}
	
	@Override
	public ITreeAutomaton<LETTER, STATE> getResult() {
		return result;
	}

	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
}
