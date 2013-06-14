package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;


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
	INestedWordAutomatonSimple<LETTER,STATE> m_Nwa;
	private final boolean m_UseDoubleDeckers;
	int maxDegreeOfNondeterminism = 0;
	
	public PowersetDeterminizer(INestedWordAutomatonSimple<LETTER,STATE> nwa, 
			boolean useDoubleDeckers) { 
		m_Nwa = nwa;
		m_UseDoubleDeckers = useDoubleDeckers;
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
				for (OutgoingInternalTransition<LETTER, STATE> upSucc : m_Nwa.internalSuccessors(upState, symbol)) {
					succDetState.addPair(downState,upSucc.getSucc(), m_Nwa);
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
				for (OutgoingCallTransition<LETTER, STATE> upSucc : m_Nwa.callSuccessors(upState, symbol)) {
					STATE succDownState;
					// if !m_UseDoubleDeckers we always use getEmptyStackState()
					// as down state to obtain sets of states instead of
					// sets of DoubleDeckers.
					if (m_UseDoubleDeckers) {
						succDownState = upState;
					} else {
						succDownState = m_Nwa.getEmptyStackState();
					}
					succDetState.addPair(succDownState,upSucc.getSucc(), m_Nwa);
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
					for (OutgoingReturnTransition<LETTER, STATE> upSucc : m_Nwa.returnSucccessors(upState, upLinPred, symbol)) {
						succDetState.addPair(downLinPred, upSucc.getSucc(), m_Nwa);
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


	@Override
	public boolean useDoubleDeckers() {
		return m_UseDoubleDeckers;
	}
	
	
	
}
