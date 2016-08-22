package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;

public class Complement<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomaton<LETTER, STATE> tree;
	
	protected final ITreeAutomaton<LETTER, STATE> res;
	
	public Complement(ITreeAutomaton<LETTER, STATE> tree) {
		this.tree = tree;
		
		this.res = computeResult();
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
	
	private TreeAutomatonBU<LETTER, STATE> computeResult() {
		Determinize<LETTER, STATE> op = new Determinize<LETTER, STATE>(tree);
		TreeAutomatonBU<LETTER, STATE> res = (TreeAutomatonBU<LETTER, STATE>) op.res;
		res.complementFinals();
		
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

}
