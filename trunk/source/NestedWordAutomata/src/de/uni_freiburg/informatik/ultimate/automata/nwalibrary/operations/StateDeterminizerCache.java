package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;

public class StateDeterminizerCache<LETTER, STATE> implements
		IStateDeterminizer<LETTER, STATE> {
	
	
	private final IStateDeterminizer<LETTER, STATE> m_StateDeterminizer;
	
	Map<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>	m_InternalSuccessorCache =
	new HashMap<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>();
	
	Map<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>	m_CallSuccessorCache =
		new HashMap<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>();
	
	Map<DeterminizedState<LETTER,STATE>,Map<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>> 
	 m_ReturnSuccessorCache = new HashMap<DeterminizedState<LETTER,STATE>,
		Map<DeterminizedState<LETTER,STATE>,Map<LETTER,DeterminizedState<LETTER,STATE>>>>();

	int m_InternalSuccs = 0;
	int m_InternalSuccsCache = 0;
	int m_CallSuccs = 0;
	int m_CallSuccsCache = 0;
	int m_ReturnSuccs = 0;
	int m_ReturnSuccsCache = 0;
	int m_Unnecessary = 0;
	
	
	public StateDeterminizerCache(
			IStateDeterminizer<LETTER, STATE> stateDeterminizer) {
		m_StateDeterminizer = stateDeterminizer;
	}

	@Override
	public DeterminizedState<LETTER, STATE> initialState() {
		return m_StateDeterminizer.initialState();
	}

	
	@Override
	public DeterminizedState<LETTER, STATE> internalSuccessor(
			DeterminizedState<LETTER, STATE> detState, LETTER symbol) {
		DeterminizedState<LETTER, STATE> detSucc;
		detSucc = internalSuccessorCache(detState, symbol);
		if (detSucc == null) {
			detSucc = m_StateDeterminizer.internalSuccessor(detState, symbol);
			putInternalSuccessorCache(detState, symbol, detSucc);
			m_InternalSuccs++;
		} else {
			m_InternalSuccsCache++;
		}
		return detSucc;
	}


	@Override
	public DeterminizedState<LETTER, STATE> callSuccessor(
			DeterminizedState<LETTER, STATE> detState, LETTER symbol) {
		DeterminizedState<LETTER, STATE> detSucc;
		detSucc = callSuccessorCache(detState, symbol);
		if (detSucc == null) {
			detSucc = m_StateDeterminizer.callSuccessor(detState, symbol);
			putCallSuccessorCache(detState, symbol, detSucc);
			m_CallSuccs++;
		} else {
			m_CallSuccsCache++;
		}
		return detSucc;
	}


	@Override
	public DeterminizedState<LETTER, STATE> returnSuccessor(
			DeterminizedState<LETTER, STATE> detState,
			DeterminizedState<LETTER, STATE> hierPred, LETTER symbol) {
		DeterminizedState<LETTER, STATE> detSucc;
		detSucc = returnSuccessorCache(detState, hierPred, symbol);
		if (detSucc == null) {
			detSucc = m_StateDeterminizer.returnSuccessor(detState, hierPred, symbol);
			putReturnSuccessorCache(detState, hierPred, symbol, detSucc);
			m_ReturnSuccs++;
		} else {
			m_ReturnSuccsCache++;
		}
		return detSucc;
	}

	@Override
	public int getMaxDegreeOfNondeterminism() {
		return m_StateDeterminizer.getMaxDegreeOfNondeterminism();
	}
	
	

	private DeterminizedState<LETTER,STATE> internalSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			LETTER symbol) {
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			m_InternalSuccessorCache.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putInternalSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			LETTER symbol,
			DeterminizedState<LETTER,STATE>  succ) {
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			m_InternalSuccessorCache.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<LETTER,DeterminizedState<LETTER,STATE>>();
			m_InternalSuccessorCache.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);	
	}
	
	
	
	private DeterminizedState<LETTER,STATE> callSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			LETTER symbol) {
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			m_CallSuccessorCache.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putCallSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			LETTER symbol,
			DeterminizedState<LETTER,STATE>  succ) {
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			m_CallSuccessorCache.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<LETTER,DeterminizedState<LETTER,STATE>>();
			m_CallSuccessorCache.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);	
	}
	
	private DeterminizedState<LETTER,STATE> returnSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			DeterminizedState<LETTER,STATE> linPred,
			LETTER symbol) {
		Map<DeterminizedState<LETTER,STATE>,Map<LETTER, DeterminizedState<LETTER,STATE>>> linPred2symbol2succ =
			m_ReturnSuccessorCache.get(linPred);
		if (linPred2symbol2succ == null) {
			return null;
		}
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			linPred2symbol2succ.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putReturnSuccessorCache(
			DeterminizedState<LETTER,STATE>  state,
			DeterminizedState<LETTER,STATE> linPred,
			LETTER symbol,
			DeterminizedState<LETTER,STATE>  succ) {
		Map<DeterminizedState<LETTER,STATE>,Map<LETTER, DeterminizedState<LETTER,STATE>>> linPred2symbol2succ =
			m_ReturnSuccessorCache.get(linPred);
		if (linPred2symbol2succ == null) {
			linPred2symbol2succ = 
				new HashMap<DeterminizedState<LETTER,STATE>,Map<LETTER, DeterminizedState<LETTER,STATE>>>();
			m_ReturnSuccessorCache.put(linPred, linPred2symbol2succ);
		}
		Map<LETTER, DeterminizedState<LETTER,STATE>> symbol2succ = 
			linPred2symbol2succ.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<LETTER,DeterminizedState<LETTER,STATE>>();
			linPred2symbol2succ.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);	
	}

}
