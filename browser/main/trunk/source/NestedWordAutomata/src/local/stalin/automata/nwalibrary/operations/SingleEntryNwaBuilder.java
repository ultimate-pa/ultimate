package local.stalin.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.nwalibrary.DoubleDecker;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;

public class SingleEntryNwaBuilder<S,C> extends DoubleDeckerGraphBuilder<S,C> {

	private final INestedWordAutomaton<S, C> m_input;
	
	private final Map<IState<S,C>,IState<S,C>> newState2oldState = 
		new HashMap<IState<S,C>,IState<S,C>>();
	
	private final Map<IState<S,C>,Map<S,IState<S,C>>> m_oldStateAndCall2NewState =
		new HashMap<IState<S,C>,Map<S,IState<S,C>>>();
	private final Map<IState<S,C>,IState<S,C>> m_oldStateAndNoCall2NewState = 
		new HashMap<IState<S,C>,IState<S,C>>();
	
	private final Map<IState<S,C>,S> m_NewState2Call =
		new HashMap<IState<S,C>,S>();
	private final Set<IState<S,C>> m_NewStateWithoutCall = 
		new HashSet<IState<S,C>>();
	
	boolean m_verify = false;

	
	/**
	 * Given an INestedWordAutomaton nwa return an INestedWordAutomaton
	 * <ul>
	 * <li> that accepts the same language
	 * <li> where every state has a no preceeding call statement or a unique
	 * call statement
	 * </ul>
	 * @param nwa
	 */
	public SingleEntryNwaBuilder (INestedWordAutomaton<S,C> nwa) {
		m_input = nwa;
		result = new NestedWordAutomaton<S,C>(nwa.getInternalAlphabet(),
											  nwa.getCallAlphabet(),
											  nwa.getReturnAlphabet(),
											  nwa.getContentFactory());
		newState2oldState.put(
					result.getEmptyStackState(), m_input.getEmptyStackState());
		computeResult();
	}
	
	
	
	/**
	 * For debugging only. Set verify to true to check if result fulfills the
	 * following property:
	 * every state has a no preceeding call statement or a unique
	 * call statement
	 */
	public SingleEntryNwaBuilder (INestedWordAutomaton<S,C> nwa, boolean verify) {
		m_input = nwa;
		result = new NestedWordAutomaton<S,C>(nwa.getInternalAlphabet(),
											  nwa.getCallAlphabet(),
											  nwa.getReturnAlphabet(),
											  nwa.getContentFactory());
		newState2oldState.put(
					result.getEmptyStackState(), m_input.getEmptyStackState());
		m_verify = verify;
		computeResult();
	}
	
	
	
	
	private IState<S,C> getNewStates(IState<S,C> oldState, 
					boolean isInitial, S call) {
		if (call == null) {
			IState<S,C> newState = m_oldStateAndNoCall2NewState.get(oldState);
			if (newState == null) {
				newState = result.addState(isInitial, 
						m_input.isFinal(oldState), oldState.getContent());
				newState2oldState.put(newState, oldState);
				m_oldStateAndNoCall2NewState.put(oldState, newState);
				m_NewStateWithoutCall.add(newState);
			}
			return newState;
		}
		else {
			IState<S,C> newState = null;
			Map<S, IState<S, C>> call2newState = 
				m_oldStateAndCall2NewState.get(oldState);
			if (call2newState != null) {
				newState = call2newState.get(call);
			}
			if (newState == null) {
				newState = result.addState(isInitial, 
						m_input.isFinal(oldState), oldState.getContent());
				newState2oldState.put(newState, oldState);
				m_oldStateAndNoCall2NewState.put(oldState, newState);
				if (call2newState == null) {
					call2newState = new HashMap<S,IState<S,C>>();
					m_oldStateAndCall2NewState.put(oldState, call2newState);
				}
				m_NewState2Call.put(newState,call);
				call2newState.put(call, newState);
			}
			return newState;
		}
	}
	
	@Override
	protected Collection<IState<S,C>> computeInitialStates() {
		List<IState<S,C>> newInitialStates = 
			new ArrayList<IState<S,C>>(m_input.getInitialStates().size());
		for (IState<S,C> oldState : m_input.getInitialStates()) {
			IState<S, C> newState = getNewStates(oldState,true,null);
			newInitialStates.add(newState);
		}
		return newInitialStates;
	}

	

	@Override
	protected Collection<IState<S, C>> computeCallSuccessors(
			DoubleDecker<S,C> state) {
		List<IState<S,C>> succs = new ArrayList<IState<S,C>>();
		IState<S,C> newState = state.getUp();
		IState<S,C> oldState = newState2oldState.get(newState);
		for (S symbol : oldState.getSymbolsCall()) {
			for (IState<S,C> oldSucc : oldState.getCallSucc(symbol)) {
				IState<S, C> newSucc = getNewStates(oldSucc, false, symbol);
				result.addCallTransition(newState, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;		
	}


	@Override
	protected Collection<IState<S, C>> computeInternalSuccessors(
			DoubleDecker<S, C> state) {
		ArrayList<IState<S,C>> succs = new ArrayList<IState<S,C>>();
		IState<S,C> newState = state.getUp();
		IState<S,C> oldState = newState2oldState.get(newState);
		
		S call = m_NewState2Call.get(newState);
		if (call == null) {
			assert(m_NewStateWithoutCall.contains(newState));
		}
		for (S symbol : oldState.getSymbolsInternal()) {
			for (IState<S,C> oldSucc : oldState.getInternalSucc(symbol)) {
				IState<S, C> newSucc = getNewStates(oldSucc, false, call);
				result.addInternalTransition(newState, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;	
	}
	

	@Override
	protected Collection<IState<S, C>> computeReturnSuccessors(
			DoubleDecker<S, C> state) {
		ArrayList<IState<S,C>> succs = new ArrayList<IState<S,C>>();
		IState<S,C> newState = state.getUp();
		IState<S,C> newLinPred = state.getDown();
		IState<S,C> oldState = newState2oldState.get(newState);
		IState<S,C> oldLinPred = newState2oldState.get(newLinPred);
		
		S call = m_NewState2Call.get(newLinPred);
		if (call == null) {
			assert(m_NewStateWithoutCall.contains(newLinPred) ||
					newLinPred == result.getEmptyStackState());
		}
		
		for (S symbol : oldState.getSymbolsReturn()) {
			for (IState<S,C> oldSucc : oldState.getReturnSucc(oldLinPred,symbol)) {
				IState<S,C> newSucc = getNewStates(oldSucc, false, call);
				result.addReturnTransition(newState, newLinPred, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;	
	}
	
	
}