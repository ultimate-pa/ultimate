package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class DeterminizeSadd<LETTER,STATE> implements IOperation {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private Map<Macrostate,STATE> macrostate2detState =
		new HashMap<Macrostate, STATE>();
	private final Map<STATE,Macrostate> detState2macrostate =
		new HashMap<STATE, Macrostate>();
	private Map<STATE,Set<STATE>> summary = 
		new HashMap<STATE, Set<STATE>>();
	private final STATE auxilliaryEmptyStackState;
	private final INestedWordAutomaton<LETTER,STATE> m_Operand;
	private final INestedWordAutomaton<LETTER,STATE> result;
	
	private final List<StatePair> queue = new LinkedList<StatePair>();
	
	// set of pairs that has been visited. The first state of the pair can be any automaton
	// state, the second state is a state that has an outgoing call transition.
	private final Map<STATE,Set<STATE>> visited = 
		new HashMap<STATE, Set<STATE>>();
	
	
	@Override
	public String operationName() {
		return "determinizeSadd";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
			result.sizeInformation();
	}
	
	
	
	public DeterminizeSadd(INestedWordAutomaton<LETTER,STATE> nwa) {
		m_Operand = nwa;
		s_Logger.info(startMessage());
		result = new NestedWordAutomaton<LETTER,STATE>(
				m_Operand.getInternalAlphabet(),
				m_Operand.getCallAlphabet(),
				m_Operand.getReturnAlphabet(),
				m_Operand.getStateFactory());
		auxilliaryEmptyStackState = m_Operand.getEmptyStackState();
		determinize();
		s_Logger.info(exitMessage());
	}
	
	public INestedWordAutomaton<LETTER,STATE> getResult() throws OperationCanceledException {
		assert (ResultChecker.determinize(m_Operand, result));
		return result;
	}
	
	public boolean wasVisited(STATE state, STATE callerState) {
		Set<STATE> callerStates = visited.get(state);
		if (callerStates == null) {
			return false;
		}
		else {
			return callerStates.contains(callerState);
		}
	}
	
	public void markVisited(STATE state, STATE callerState) {
		Set<STATE> callerStates = visited.get(state);
		if (callerStates == null) {
			callerStates = new HashSet<STATE>();
			visited.put(state, callerStates);
		}
		callerStates.add(callerState);
	}
	
	public void addSummary(STATE summaryPred, STATE summarySucc) {
		Set<STATE> summarySuccessors = summary.get(summaryPred);
		if (summarySuccessors == null) {
			summarySuccessors = new HashSet<STATE>();
			summary.put(summaryPred, summarySuccessors);
		}
		summarySuccessors.add(summarySucc);
	}
	
	
	
	public void enqueueAndMark(STATE state, STATE callerState) {
		if (!wasVisited(state, callerState)) {
			markVisited(state, callerState);
			StatePair statePair = new StatePair(state,callerState);
			queue.add(statePair);
		}
	}
	
	private Set<STATE> getKnownCallerStates(STATE state) {
		Set<STATE> callerStates = visited.get(state);
		if (callerStates == null) {
			return new HashSet<STATE>(0);
		}
		else {
			return callerStates;
		}
	}
	
	private void determinize() {
		s_Logger.debug("Starting determinizeSadd. Operand " + m_Operand.sizeInformation());
		Macrostate initialMacroState = new Macrostate();

		for (STATE state : m_Operand.getInitialStates()) {
			initialMacroState.addPair(state, auxilliaryEmptyStackState);
		}
		STATE initialDetState = initialMacroState.getContent();
		result.addState(true, initialMacroState.isFinal, initialDetState);
		macrostate2detState.put(initialMacroState, initialDetState);
		detState2macrostate.put(initialDetState, initialMacroState);
		enqueueAndMark(initialDetState,auxilliaryEmptyStackState);
		
		while(!queue.isEmpty()) {
			StatePair statePair = queue.remove(0);
//			s_Logger.debug("Processing: "+ statePair);
			processStatePair(statePair);
			if (summary.containsKey(statePair.state)) {
				for (STATE summarySucc : summary.get(statePair.state)) {
					enqueueAndMark(summarySucc, statePair.callerState);
				}
				
			}
		}
		assert result.isDeterministic();
	}
	
	
//	private void processSummary(IState<LETTER,STATE> summaryPred, IState<LETTER,STATE> summaryPredCaller)
	
	
	private void processStatePair(StatePair statePair) {
		STATE detState = statePair.state;
		Macrostate macrostate = detState2macrostate.get(detState);
		
		Set<LETTER> symbolsInternal = new HashSet<LETTER>();
		for (STATE state : macrostate.getStates()) {
			symbolsInternal.addAll(m_Operand.lettersInternal(state));
		}
		for (LETTER symbol : symbolsInternal) {
			Macrostate succMacrostate = internalSuccMacrostate(macrostate, symbol);
			STATE succDetState = macrostate2detState.get(succMacrostate);
			if (succDetState == null) {
				succDetState = succMacrostate.getContent();
				result.addState(false, succMacrostate.isFinal, succDetState);
				macrostate2detState.put(succMacrostate, succDetState);
				detState2macrostate.put(succDetState, succMacrostate);
			}
			result.addInternalTransition(detState, symbol, succDetState);
			enqueueAndMark(succDetState, statePair.callerState);
		}
		
		
		
		Set<LETTER> symbolsCall = new HashSet<LETTER>();
		for (STATE state : macrostate.getStates()) {
			symbolsCall.addAll(m_Operand.lettersCall(state));
		}
		for (LETTER symbol : symbolsCall) {
			Macrostate succMacrostate = callSuccMacrostate(macrostate, symbol);
			STATE succDetState = macrostate2detState.get(succMacrostate);
			if (succDetState == null) {
				succDetState = succMacrostate.getContent();
				result.addState(false, succMacrostate.isFinal, succDetState);
				macrostate2detState.put(succMacrostate, succDetState);
				detState2macrostate.put(succDetState, succMacrostate);
			}
			result.addCallTransition(detState, symbol, succDetState);
			enqueueAndMark(succDetState, detState);
		}
		
		
		STATE detLinPred = statePair.callerState;
		if (detLinPred != auxilliaryEmptyStackState) {
		
			Set<LETTER> symbolsReturn = new HashSet<LETTER>();
			for (STATE state : macrostate.getStates()) {
				symbolsReturn.addAll(m_Operand.lettersReturn(state));
			}
			for (LETTER symbol : symbolsReturn) {
				Macrostate linPredMacrostate = detState2macrostate.get(detLinPred);
				Macrostate succMacrostate = returnSuccMacrostate(macrostate, linPredMacrostate, symbol);
				if (!succMacrostate.getStates().isEmpty()) {
					STATE succDetState = macrostate2detState.get(succMacrostate);
					if (succDetState == null) {
						succDetState = succMacrostate.getContent();
						result.addState(false, succMacrostate.isFinal, succDetState);
						macrostate2detState.put(succMacrostate, succDetState);
						detState2macrostate.put(succDetState, succMacrostate);
					}
					result.addReturnTransition(detState, detLinPred, symbol, succDetState);
					addSummary(detLinPred, succDetState);
					for (STATE detLinPredCallerState : getKnownCallerStates(detLinPred)) {
						enqueueAndMark(succDetState, detLinPredCallerState);
					}
				}

			}
		
		}

		
	}
	
	
	/**
	 * Compute successor Macrostate under internal transition of a Macrostate
	 * and symbol. 
	 */
	private Macrostate internalSuccMacrostate(Macrostate macrostate, LETTER symbol) {
		Macrostate succMacrostate = new Macrostate();
		for (STATE state : macrostate.getStates()) {
			for (STATE succ : m_Operand.succInternal(state, symbol)) {
				Set<STATE> callerStates = macrostate.getCallerStates(state);
				succMacrostate.addPairs(succ,callerStates);
			}
		}
		return succMacrostate;	
	}
	
	/**
	 * Compute successor Macrostate under call transition of a Macrostate
	 * and symbol. 
	 */
	private Macrostate callSuccMacrostate(Macrostate macrostate, LETTER symbol) {
		Macrostate succMacrostate = new Macrostate();
		for (STATE state : macrostate.getStates()) {
			for (STATE succ : m_Operand.succCall(state, symbol)) {
				succMacrostate.addPair(succ,state);
			}
		}
		return succMacrostate;	
	}

	
	/**
	 * Compute successor Macrostate under return transition of a Macrostate,
	 * a linear predecessor Macrostate and a symbol. 
	 */
	private Macrostate returnSuccMacrostate(Macrostate macrostate,
								Macrostate linPredMacrostate, LETTER symbol) {
		Macrostate succMacrostate = new Macrostate();
		for (STATE state : macrostate.getStates()) {
			for (STATE linPred : macrostate.getCallerStates(state)) {
				for (STATE succ : m_Operand.succReturn(state, linPred, symbol)) {
					Set<STATE> callerStates = 
						linPredMacrostate.getCallerStates(linPred);
					if (callerStates != null) {
						succMacrostate.addPairs(succ,callerStates);
					}
				}
			}
		}
		return succMacrostate;	
	}
	



	private class StatePair {
		private final STATE state;
		private final STATE callerState;
		private final int m_hashCode;
		public StatePair(STATE state, STATE callerState) {
			this.state = state;
			this.callerState = callerState;
			m_hashCode = 3 * state.hashCode() + 5 * callerState.hashCode(); 
		}

		public boolean equals(StatePair statePair) {
			return state.equals(statePair.state) && 
									callerState.equals(statePair.callerState);
		}
		
		public int hashCode() {
			return m_hashCode;
		}
		
		public String toString() {
			return "CallerState: " + callerState + "  State: "+ state;
		}
		
	}
	
	/**
	 * List of pairs of States
	 *
	 * @param <LETTER> Symbol
	 * @param <STATE> Content
	 */
	private class Macrostate {
		private final Map<STATE,Set<STATE>> pairList =
			new HashMap<STATE, Set<STATE>>();
		private boolean isFinal = false;
		
		Set<STATE> getStates() {
			return pairList.keySet();
		}
		
		Set<STATE> getCallerStates(STATE state) {
			return pairList.get(state);
		}
		
		boolean isFinal() {
			return isFinal;
		}
		
		STATE getContent() {
			return result.getStateFactory().determinize(pairList);
		}
		
		private void addPair(STATE state, STATE callerState) {
			if (m_Operand.isFinal(state)) {
				isFinal = true;
			}
			Set<STATE> callerStates = pairList.get(state);
			if (callerStates == null) {
				callerStates = new HashSet<STATE>();
				pairList.put(state, callerStates);
			}
			callerStates.add(callerState);
		}
		
		private void addPairs(STATE state, 
											Set<STATE> newCallerStates){
			if (m_Operand.isFinal(state)) {
				isFinal = true;
			}
			Set<STATE> callerStates = pairList.get(state);
			if (callerStates == null) {
				callerStates = new HashSet<STATE>();
				pairList.put(state, callerStates);
			}
			callerStates.addAll(newCallerStates);
		}
		

		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object obj) {
			if (obj instanceof DeterminizeSadd.Macrostate) {
				Macrostate macrostate = (Macrostate) obj;
				return pairList.equals(macrostate.pairList);
			}
			else {
				return false;
			}
		}

		@Override
		public int hashCode() {
			return pairList.hashCode();
		}
		
		public String toString() {
			return pairList.toString();
		}		
	}
	

}
