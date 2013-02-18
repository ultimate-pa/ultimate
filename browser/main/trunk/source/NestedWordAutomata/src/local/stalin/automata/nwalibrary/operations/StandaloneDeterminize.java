package local.stalin.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.Pair;
import local.stalin.automata.nwalibrary.State;

public class StandaloneDeterminize<S,C> {
	
//	private static Logger s_Logger = 
//		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private Map<Macrostate<S,C>,IState<S,C>> macrostate2detState =
		new HashMap<Macrostate<S,C>, IState<S,C>>();
	private final Map<IState<S,C>,Macrostate<S,C>> detState2macrostate =
		new HashMap<IState<S,C>, Macrostate<S,C>>();
	private Map<IState<S,C>,Set<IState<S,C>>> summary = 
		new HashMap<IState<S,C>, Set<IState<S,C>>>();
	private final IState<S,C> auxilliaryEmptyStackState;
	private final INestedWordAutomaton<S,C> m_nwa;
	private final INestedWordAutomaton<S,C> result;
	
	private final List<StatePair> queue = new LinkedList<StatePair>();
	
	// set of pairs that has been visited. The first state of the pair can be any automaton
	// state, the second state is a state that has an outgoing call transition.
	private final Map<IState<S,C>,Set<IState<S,C>>> visited = 
		new HashMap<IState<S,C>, Set<IState<S,C>>>();
	
	public StandaloneDeterminize(INestedWordAutomaton<S,C> nwa) {
		m_nwa = nwa;
		result = new NestedWordAutomaton<S, C>(
				m_nwa.getInternalAlphabet(),
				m_nwa.getCallAlphabet(),
				m_nwa.getReturnAlphabet(),
				m_nwa.getContentFactory());
		auxilliaryEmptyStackState = new State<S,C>(false,m_nwa.getContentFactory().createSinkStateContent());
	}
	
	public boolean wasVisited(IState<S,C> state, IState<S,C> callerState) {
		Set<IState<S,C>> callerStates = visited.get(state);
		if (callerStates == null) {
			return false;
		}
		else {
			return callerStates.contains(callerState);
		}
	}
	
	public void markVisited(IState<S,C> state, IState<S,C> callerState) {
		Set<IState<S,C>> callerStates = visited.get(state);
		if (callerStates == null) {
			callerStates = new HashSet<IState<S,C>>();
			visited.put(state, callerStates);
		}
		callerStates.add(callerState);
	}
	
	public void addSummary(IState<S,C> summaryPred, IState<S,C> summarySucc) {
		Set<IState<S,C>> summarySuccessors = summary.get(summaryPred);
		if (summarySuccessors == null) {
			summarySuccessors = new HashSet<IState<S,C>>();
			summary.put(summaryPred, summarySuccessors);
		}
		summarySuccessors.add(summarySucc);
	}
	
	
	
	public void enqueueAndMark(IState<S,C> state, IState<S,C> callerState) {
		if (!wasVisited(state, callerState)) {
			markVisited(state, callerState);
			StatePair statePair = new StatePair(state,callerState);
			queue.add(statePair);
		}
	}
	
	private Set<IState<S,C>> getKnownCallerStates(IState<S,C> state) {
		Set<IState<S,C>> callerStates = visited.get(state);
		if (callerStates == null) {
			return new HashSet<IState<S,C>>(0);
		}
		else {
			return callerStates;
		}
	}
	
	public INestedWordAutomaton<S,C> determinize() {

		Macrostate<S,C> initialMacroState = new Macrostate<S,C>();

		for (IState<S,C> state : m_nwa.getInitialStates()) {
			initialMacroState.addPair(state, auxilliaryEmptyStackState);
		}
		IState<S,C> initialDetState = result.addState(true, initialMacroState.isFinal, initialMacroState.getContent());
		macrostate2detState.put(initialMacroState, initialDetState);
		detState2macrostate.put(initialDetState, initialMacroState);
		enqueueAndMark(initialDetState,auxilliaryEmptyStackState);
		
		while(!queue.isEmpty()) {
			StatePair statePair = queue.remove(0);
//			s_Logger.debug("Processing: "+ statePair);
			processStatePair(statePair);
			if (summary.containsKey(statePair.state)) {
				for (IState<S,C> summarySucc : summary.get(statePair.state)) {
					enqueueAndMark(summarySucc, statePair.callerState);
				}
				
			}
		}
		assert result.isDeterministic();
		return result;
	}
	
	
//	private void processSummary(IState<S,C> summaryPred, IState<S,C> summaryPredCaller)
	
	
	private void processStatePair(StatePair statePair) {
		IState<S,C> detState = statePair.state;
		Macrostate<S,C> macrostate = detState2macrostate.get(detState);
		
		Set<S> symbolsInternal = new HashSet<S>();
		for (IState<S,C> state : macrostate.getStates()) {
			symbolsInternal.addAll(state.getSymbolsInternal());
		}
		for (S symbol : symbolsInternal) {
			Macrostate<S,C> succMacrostate = internalSuccMacrostate(macrostate, symbol);
			IState<S,C> succDetState = macrostate2detState.get(succMacrostate);
			if (succDetState == null) {
				succDetState = result.addState(false, succMacrostate.isFinal, succMacrostate.getContent());
				macrostate2detState.put(succMacrostate, succDetState);
				detState2macrostate.put(succDetState, succMacrostate);
			}
			result.addInternalTransition(detState, symbol, succDetState);
			enqueueAndMark(succDetState, statePair.callerState);
		}
		
		
		
		Set<S> symbolsCall = new HashSet<S>();
		for (IState<S,C> state : macrostate.getStates()) {
			symbolsCall.addAll(state.getSymbolsCall());
		}
		for (S symbol : symbolsCall) {
			Macrostate<S,C> succMacrostate = callSuccMacrostate(macrostate, symbol);
			IState<S,C> succDetState = macrostate2detState.get(succMacrostate);
			if (succDetState == null) {
				succDetState = result.addState(false, succMacrostate.isFinal, succMacrostate.getContent());
				macrostate2detState.put(succMacrostate, succDetState);
				detState2macrostate.put(succDetState, succMacrostate);
			}
			result.addCallTransition(detState, symbol, succDetState);
			enqueueAndMark(succDetState, detState);
		}
		
		
		IState<S,C> detLinPred = statePair.callerState;
		if (detLinPred != auxilliaryEmptyStackState) {
		
			Set<S> symbolsReturn = new HashSet<S>();
			for (IState<S,C> state : macrostate.getStates()) {
				symbolsReturn.addAll(state.getSymbolsReturn());
			}
			for (S symbol : symbolsReturn) {
				Macrostate<S,C> linPredMacrostate = detState2macrostate.get(detLinPred);
				Macrostate<S,C> succMacrostate = returnSuccMacrostate(macrostate, linPredMacrostate, symbol);
				if (!succMacrostate.getStates().isEmpty()) {
					IState<S,C> succDetState = macrostate2detState.get(succMacrostate);
					if (succDetState == null) {
						succDetState = result.addState(false, succMacrostate.isFinal, succMacrostate.getContent());
						macrostate2detState.put(succMacrostate, succDetState);
						detState2macrostate.put(succDetState, succMacrostate);
					}
					result.addReturnTransition(detState, detLinPred, symbol, succDetState);
					addSummary(detLinPred, succDetState);
					for (IState<S,C> detLinPredCallerState : getKnownCallerStates(detLinPred)) {
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
	private Macrostate<S,C> internalSuccMacrostate(Macrostate<S,C> macrostate, S symbol) {
		Macrostate<S,C> succMacrostate = new Macrostate<S,C>();
		for (IState<S,C> state : macrostate.getStates()) {
			for (IState<S,C> succ : state.getInternalSucc(symbol)) {
				Set<IState<S, C>> callerStates = macrostate.getCallerStates(state);
				succMacrostate.addPairs(succ,callerStates);
			}
		}
		return succMacrostate;	
	}
	
	/**
	 * Compute successor Macrostate under call transition of a Macrostate
	 * and symbol. 
	 */
	private Macrostate<S,C> callSuccMacrostate(Macrostate<S,C> macrostate, S symbol) {
		Macrostate<S,C> succMacrostate = new Macrostate<S,C>();
		for (IState<S,C> state : macrostate.getStates()) {
			for (IState<S,C> succ : state.getCallSucc(symbol)) {
				succMacrostate.addPair(succ,state);
			}
		}
		return succMacrostate;	
	}

	
	/**
	 * Compute successor Macrostate under return transition of a Macrostate,
	 * a linear predecessor Macrostate and a symbol. 
	 */
	private Macrostate<S,C> returnSuccMacrostate(Macrostate<S,C> macrostate,
								Macrostate<S,C> linPredMacrostate, S symbol) {
		Macrostate<S,C> succMacrostate = new Macrostate<S,C>();
		for (IState<S,C> state : macrostate.getStates()) {
			for (IState<S,C> linPred : macrostate.getCallerStates(state)) {
				for (IState<S,C> succ : state.getReturnSucc(linPred,symbol)) {
					Set<IState<S, C>> callerStates = 
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
		private final IState<S,C> state;
		private final IState<S,C> callerState;
		private final int m_hashCode;
		public StatePair(IState<S,C> state, IState<S,C> callerState) {
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
	 * @param <S> Symbol
	 * @param <C> Content
	 */
	private class Macrostate<S,C> {
		private final Map<IState<S,C>,Set<IState<S,C>>> pairList =
			new HashMap<IState<S,C>, Set<IState<S,C>>>();
		private boolean isFinal = false;
		
		Set<IState<S, C>> getStates() {
			return pairList.keySet();
		}
		
		Set<IState<S,C>> getCallerStates(IState<S,C> state) {
			return pairList.get(state);
		}
		
		boolean isFinal() {
			return isFinal;
		}
		
		C getContent() {
			Collection<Pair<C,C>> cPairList = new LinkedList<Pair<C,C>>();
			for (IState<S,C> state : pairList.keySet()) {
				for (IState<S,C> callerState : pairList.get(state)) {
					Pair<C,C> pair = new Pair<C,C>(callerState.getContent(),
															state.getContent());
					cPairList.add(pair);
				}
			}
			ContentFactory<C> cF = (ContentFactory<C>)m_nwa.getContentFactory();
			return cF.createContentOnDeterminization(cPairList);
		}
		
		private void addPair(IState<S,C> state, IState<S,C> callerState) {
			if (state.isFinal()) {
				isFinal = true;
			}
			Set<IState<S,C>> callerStates = pairList.get(state);
			if (callerStates == null) {
				callerStates = new HashSet<IState<S,C>>();
				pairList.put(state, callerStates);
			}
			callerStates.add(callerState);
		}
		
		private void addPairs(IState<S,C> state, 
											Set<IState<S,C>> newCallerStates){
			if (state.isFinal()) {
				isFinal = true;
			}
			Set<IState<S,C>> callerStates = pairList.get(state);
			if (callerStates == null) {
				callerStates = new HashSet<IState<S,C>>();
				pairList.put(state, callerStates);
			}
			callerStates.addAll(newCallerStates);
		}
		

		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object obj) {
			if (obj instanceof Macrostate) {
				Macrostate<S,C> macrostate = (Macrostate<S,C>) obj;
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
