package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DNFAsBitSetList;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SalomAA;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class SAAUnion<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	
	SalomAA<LETTER, STATE> m_result;
	
	public SAAUnion(SalomAA<LETTER, STATE> a1, SalomAA<LETTER, STATE> a2) {
		assert a1.getAlphabet().equals(a2.getAlphabet());
		m_result = new SalomAA<LETTER, STATE>(a1.getLogger(), a1.getAlphabet(), a1.getStateFactory());
		
		int noStatesInA1 = a1.getStateList().size();
		
		//make the union of the statelists as sets --> otherwise there may be duplicates
		// this may make the language bigger that the union, right? But as the Hoare triples 
		// hold, it should be sound, right??
		HashSet<STATE> a1StateSet = new HashSet<>(a1.getStateList());
		HashSet<STATE> a2StateSet = new HashSet<>(a2.getStateList());
		HashSet<STATE> newStateSet = new HashSet<>();
		newStateSet.addAll(a1StateSet);
		newStateSet.addAll(a2StateSet);

		BitSet newFinalStates = new BitSet();
		ArrayList<STATE> newStateList = new ArrayList<>(newStateSet);
		HashMap<STATE, Integer> newStateToIndex = new HashMap<>();
		for (int i = 0; i < newStateList.size(); i++) {
			STATE newState = newStateList.get(i);
			newStateToIndex.put(newState, i);
			if (a1.getFinalStates().get(a1.getStateToIndex().get(newState)) 
					|| a2.getFinalStates().get(a2.getStateToIndex().get(newState))) {
				newFinalStates.set(i);
			}
		}
		m_result.setStateList(newStateList);
		m_result.setStateToIndex(newStateToIndex);
		
		newFinalStates.or(a1.getFinalStates());
		for (int i = 0; i < a2.getStateList().size(); i++) {
			if (a2.getFinalStates().get(i))
				newFinalStates.set(i + noStatesInA1);
		}
		m_result.setFinalStates(newFinalStates);
		
		DNFAsBitSetList newAcceptingFunction = a1.getAcceptingFunction().rewriteWithNewStateList(a1.getStateList(), newStateToIndex);
		newAcceptingFunction.insert(a2.getAcceptingFunction().rewriteWithNewStateList(a2.getStateList(), newStateToIndex));
		m_result.setAcceptingFunction(newAcceptingFunction);
		
		HashMap<STATE, HashMap<LETTER, DNFAsBitSetList>> newTransitionFunction = new HashMap<>();
		for (Entry<STATE, HashMap<LETTER, DNFAsBitSetList>> en1 : a1.getTransitionFunction().entrySet()) {
			newTransitionFunction.put(en1.getKey(), new HashMap<LETTER, DNFAsBitSetList>());
			for (Entry<LETTER, DNFAsBitSetList> en2 : a1.getTransitionFunction().get(en1.getKey()).entrySet()) {
				newTransitionFunction.get(en1.getKey()).put(en2.getKey(), 
						en2.getValue().rewriteWithNewStateList(a1.getStateList(), newStateToIndex));
			}
		}
		for (Entry<STATE, HashMap<LETTER, DNFAsBitSetList>> en1 : a2.getTransitionFunction().entrySet()) {
			newTransitionFunction.put(en1.getKey(), new HashMap<LETTER, DNFAsBitSetList>());
			for (Entry<LETTER, DNFAsBitSetList> en2 : a2.getTransitionFunction().get(en1.getKey()).entrySet()) {
				if (newTransitionFunction.get(en1.getKey()).get(en2.getKey()) == null) {
					newTransitionFunction.get(en1.getKey()).put(en2.getKey(), 
							en2.getValue().rewriteWithNewStateList(a2.getStateList(), newStateToIndex));
				} else {
					newTransitionFunction.get(en1.getKey()).get(en2.getKey())
							.insert(en2.getValue().rewriteWithNewStateList(a2.getStateList(), newStateToIndex));
				}
			}
		}	
		m_result.setTransitionFunction(newTransitionFunction);
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
