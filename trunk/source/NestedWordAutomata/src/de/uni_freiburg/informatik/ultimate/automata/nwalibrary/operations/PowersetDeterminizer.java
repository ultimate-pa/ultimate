package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;


/**
 * Construct deterministic states like in the classical powerset construction.
 * For determinization of NWAs there is also a powerset construction. This
 * class implements the computation of deterministic successor states according
 * to this powerset construction.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER> Symbol
 * @param <STATE> Content
 */
public class PowersetDeterminizer<LETTER,STATE> 
			implements IStateDeterminizer<LETTER,STATE> {

	StateFactory<STATE> m_ContentFactory;
	INestedWordAutomatonOldApi<LETTER,STATE> m_Nwa;
	int maxDegreeOfNondeterminism = 0;
	
	public PowersetDeterminizer(INestedWordAutomatonOldApi<LETTER,STATE> nwa) { 
		m_Nwa = nwa;
		this.m_ContentFactory = nwa.getStateFactory();
	}

	
	@Override
	public DeterminizedState<LETTER,STATE> initialState() {
		DeterminizedState<LETTER,STATE> detState = 
			new DeterminizedState<LETTER,STATE>(m_Nwa);
		for (STATE initialState : m_Nwa.getInitialStates()) {
			detState.addPair(m_Nwa.getEmptyStackState(), initialState, m_Nwa);
		}
		updateMaxDegreeOfNondeterminism(detState.degreeOfNondeterminism());
		return detState;
	}
	
	
	@Override
	public DeterminizedState<LETTER,STATE> internalSuccessor(
			DeterminizedState<LETTER,STATE> detState,
			LETTER symbol) {
		
		DeterminizedState<LETTER,STATE> succDetState = 
				new DeterminizedState<LETTER,STATE>(m_Nwa);
		for (STATE downState : detState.getDownStates()) {
			for (STATE upState : detState.getUpStates(downState)) {
				for (STATE upSucc : m_Nwa.succInternal(upState, symbol)) {
					succDetState.addPair(downState,upSucc, m_Nwa);
				}
			}
		}
		updateMaxDegreeOfNondeterminism(succDetState.degreeOfNondeterminism());
		return succDetState;	
	}
	


	@Override
	public DeterminizedState<LETTER,STATE> callSuccessor(
			DeterminizedState<LETTER,STATE> detState, 
			LETTER symbol) {
		
		DeterminizedState<LETTER,STATE> succDetState = 
				new DeterminizedState<LETTER,STATE>(m_Nwa);
		for (STATE downState : detState.getDownStates()) {
			for (STATE upState : detState.getUpStates(downState)) {
				for (STATE upSucc : m_Nwa.succCall(upState, symbol)) {
					succDetState.addPair(upState,upSucc, m_Nwa);
				}
			}
		}
		updateMaxDegreeOfNondeterminism(succDetState.degreeOfNondeterminism());
		return succDetState;	
	}

	

	@Override
	public DeterminizedState<LETTER,STATE> returnSuccessor(
			DeterminizedState<LETTER,STATE> detState,
			DeterminizedState<LETTER,STATE> detLinPred,
			LETTER symbol) {
		
		DeterminizedState<LETTER,STATE> succDetState = 
				new DeterminizedState<LETTER,STATE>(m_Nwa);
		
		for (STATE downLinPred : detLinPred.getDownStates()) {
			for (STATE upLinPred : detLinPred.getUpStates(downLinPred)) {
				Set<STATE> upStates = detState.getUpStates(upLinPred);
				if (upStates == null) continue;
				for (STATE upState : upStates) {
					for (STATE upSucc : m_Nwa.succReturn(upState, upLinPred, symbol)) {
						succDetState.addPair(downLinPred, upSucc, m_Nwa);
					}
				}
			}
		}
		updateMaxDegreeOfNondeterminism(succDetState.degreeOfNondeterminism());
		return succDetState;	
	}
	
	private void updateMaxDegreeOfNondeterminism(int newDegree) {
		if (newDegree > maxDegreeOfNondeterminism) {
			maxDegreeOfNondeterminism = newDegree;
		}
	}

	@Override
	public int getMaxDegreeOfNondeterminism() {
		return maxDegreeOfNondeterminism;
	}
	
	
	
}
