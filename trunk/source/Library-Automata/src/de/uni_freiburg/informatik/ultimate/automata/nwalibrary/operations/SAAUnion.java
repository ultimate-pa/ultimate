package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SalomAA;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class SAAUnion<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	
	SalomAA m_result;
	
	public SAAUnion(SalomAA a1, SalomAA a2) {
		assert a1.getAlphabet().equals(a2.getAlphabet());
		m_result = new SalomAA(a1.getLogger(), a1.getAlphabet(), a1.getStateFactory());
		
		ArrayList<STATE> newStateList = new ArrayList<>();
		newStateList.addAll(a1.getStateList());
		newStateList.addAll(a2.getStateList());
		
		HashMap<STATE, Integer> newStateToIndex = new HashMap<>();
		newStateToIndex.putAll(a1.getStateToIndex());
	}

	@Override
	public String operationName() {
		return "SAAUnion";
	}

	@Override
	public String startMessage() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String exitMessage() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
//	public Object getResult() throws OperationCanceledException {
	public SalomAA getResult() throws OperationCanceledException {
		return m_result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}

}
