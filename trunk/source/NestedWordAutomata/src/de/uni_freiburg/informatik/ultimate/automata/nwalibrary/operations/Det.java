package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;

public class Det<LETTER, STATE> implements INestedWordAutomaton<LETTER, STATE> {
	
	private final INestedWordAutomaton<LETTER, STATE> m_Operand;
	private final NestedWordAutomaton<LETTER, STATE> m_Cache;
	private final IStateDeterminizer<LETTER, STATE> m_StateDeterminizer;
	private final StateFactory<STATE> m_StateFactory;
	
	private final Map<STATE,DeterminizedState<LETTER, STATE>> m_res2det =
			new HashMap<STATE,DeterminizedState<LETTER, STATE>>();
	private final Map<DeterminizedState<LETTER, STATE>, STATE> m_det2res =
			new HashMap<DeterminizedState<LETTER, STATE>, STATE>();
	
	public Det(INestedWordAutomaton<LETTER, STATE> operand, 
			IStateDeterminizer<LETTER, STATE> stateDeterminizer, 
			StateFactory<STATE> sf) {
		m_Operand = operand;
		m_StateDeterminizer = stateDeterminizer;
		m_StateFactory = sf;
		m_Cache = new NestedWordAutomaton<LETTER, STATE>(operand.getAlphabet(), 
				operand.getCallAlphabet(), operand.getReturnAlphabet(), sf);
		
	}
	

	@Override
	public IRun<LETTER, STATE> acceptingRun() throws OperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean accepts(Word<LETTER> word) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public Collection<LETTER> getAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> getInternalAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> getCallAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> getReturnAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> getStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> getInitialStates() {
		if (m_Cache.getInitialStates().iterator().hasNext()) {
			
		}
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> getFinalStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isInitial(STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFinal(STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void addState(boolean isInitial, boolean isFinal, STATE state) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void removeState(STATE state) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public STATE getEmptyStackState() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersInternal(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersCall(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersReturn(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersInternalIncoming(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersCallIncoming(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersReturnIncoming(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersReturnSummary(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> succInternal(STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succInternal(state, letter);
		if (succs == null) {
			DeterminizedState<LETTER, STATE> det = m_res2det.get(state);
			assert (det != null);
			DeterminizedState<LETTER, STATE> detSucc = 
					m_StateDeterminizer.internalSuccessor(det, letter);
			STATE resSucc = m_det2res.get(detSucc);
			if (resSucc == null) {
				resSucc = detSucc.getContent(m_StateFactory);
				m_det2res.put(detSucc, resSucc);
			}
			// FIXME: continue here !!!!!!!!!!!!!!!!!!111111;
			
		}
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> succCall(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> hierPred(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> predInternal(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> predCall(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> predReturnLin(STATE state, LETTER letter,
			STATE hier) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> predReturnHier(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void addInternalTransition(STATE pred, LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void addCallTransition(STATE pred, LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void addReturnTransition(STATE pred, STATE hier, LETTER letter,
			STATE succ) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean finalIsTrap() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isDeterministic() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isTotal() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public NestedRun<LETTER, STATE> included(
			INestedWordAutomaton<LETTER, STATE> nwa)
			throws OperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public NestedLassoRun<LETTER, STATE> buchiIncluded(
			INestedWordAutomaton<LETTER, STATE> nwa)
			throws OperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> getSummaryReturnTransitions(
			LETTER letter, STATE hier) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> getIncomingReturnTransitions(
			LETTER letter, STATE hier) {
		// TODO Auto-generated method stub
		return null;
	}

}
