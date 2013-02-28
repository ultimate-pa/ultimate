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
		constructInitialState();
	}
	
	private void constructInitialState() {
		DeterminizedState<LETTER, STATE> initialDet = 
				m_StateDeterminizer.initialState();
		STATE initialState = initialDet.getContent(m_StateFactory);
		m_det2res.put(initialDet, initialState);
		m_Cache.addState(true, initialDet.containsFinal(), initialState);
	}
	
	private STATE getOrConstructState(DeterminizedState<LETTER, STATE> detState) {
		STATE state = m_det2res.get(detState);
		if (state == null) {
			state = detState.getContent(m_StateFactory);
			m_det2res.put(detState, state);
			m_res2det.put(state, detState);
			m_Cache.addState(false, detState.containsFinal(), state);
		}
		return state;
	}
	

	@Override
	public IRun<LETTER, STATE> acceptingRun() throws OperationCanceledException {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean accepts(Word<LETTER> word) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int size() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<LETTER> getAlphabet() {
		return m_Operand.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<LETTER> getInternalAlphabet() {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Collection<LETTER> getCallAlphabet() {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Collection<LETTER> getReturnAlphabet() {
		return m_Operand.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_Operand.getStateFactory();
	}

	@Override
	public Collection<STATE> getStates() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<STATE> getInitialStates() {
		return m_Cache.getInitialStates();
	}

	@Override
	public Collection<STATE> getFinalStates() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isInitial(STATE state) {
		return m_Cache.isInitial(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return m_Cache.isFinal(state);
	}

	@Override
	public void addState(boolean isInitial, boolean isFinal, STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void removeState(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public STATE getEmptyStackState() {
		return m_Cache.getEmptyStackState();
	}

	@Override
	public Collection<LETTER> lettersInternal(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<LETTER> lettersCall(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<LETTER> lettersReturn(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<LETTER> lettersInternalIncoming(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<LETTER> lettersCallIncoming(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<LETTER> lettersReturnIncoming(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<LETTER> lettersReturnSummary(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<STATE> succInternal(STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succInternal(state, letter);
		if (succs == null) {
			DeterminizedState<LETTER, STATE> detState = m_res2det.get(state);
			assert (detState != null);
			DeterminizedState<LETTER, STATE> detSucc = 
					m_StateDeterminizer.internalSuccessor(detState, letter);
			STATE succ = getOrConstructState(detSucc);
			m_Cache.addInternalTransition(state, letter, succ);
		}
		return m_Cache.succInternal(state, letter);
	}

	@Override
	public Collection<STATE> succCall(STATE state, LETTER letter) {
		Collection<STATE> succs = m_Cache.succCall(state, letter);
		if (succs == null) {
			DeterminizedState<LETTER, STATE> detState = m_res2det.get(state);
			assert (detState != null);
			DeterminizedState<LETTER, STATE> detSucc = 
					m_StateDeterminizer.callSuccessor(detState, letter);
			STATE succ = getOrConstructState(detSucc);
			m_Cache.addCallTransition(state, letter, succ);
		}
		return m_Cache.succCall(state, letter);
	}

	@Override
	public Collection<STATE> hierPred(STATE state, LETTER letter) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		Collection<STATE> succs = m_Cache.succReturn(state, hier, letter);
		if (succs == null) {
			DeterminizedState<LETTER, STATE> detState = m_res2det.get(state);
			assert (detState != null);
			DeterminizedState<LETTER, STATE> detHier = m_res2det.get(hier);
			assert (detHier != null);
			DeterminizedState<LETTER, STATE> detSucc = 
					m_StateDeterminizer.returnSuccessor(detState, detHier, letter);
			STATE succ = getOrConstructState(detSucc);
			m_Cache.addReturnTransition(state, hier, letter, succ);
		}
		return m_Cache.succReturn(state, hier, letter);
	}

	@Override
	public Collection<STATE> predInternal(STATE state, LETTER letter) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<STATE> predCall(STATE state, LETTER letter) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<STATE> predReturnLin(STATE state, LETTER letter,
			STATE hier) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Collection<STATE> predReturnHier(STATE state, LETTER letter) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void addInternalTransition(STATE pred, LETTER letter, STATE succ) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void addCallTransition(STATE pred, LETTER letter, STATE succ) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void addReturnTransition(STATE pred, STATE hier, LETTER letter,
			STATE succ) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean finalIsTrap() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isDeterministic() {
		return true;
	}

	@Override
	public boolean isTotal() {
		throw new UnsupportedOperationException();
	}

	@Override
	public NestedRun<LETTER, STATE> included(
			INestedWordAutomaton<LETTER, STATE> nwa)
			throws OperationCanceledException {
		throw new UnsupportedOperationException();
	}

	@Override
	public NestedLassoRun<LETTER, STATE> buchiIncluded(
			INestedWordAutomaton<LETTER, STATE> nwa)
			throws OperationCanceledException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> getSummaryReturnTransitions(
			LETTER letter, STATE hier) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> getIncomingReturnTransitions(
			LETTER letter, STATE hier) {
		throw new UnsupportedOperationException();
	}

}
