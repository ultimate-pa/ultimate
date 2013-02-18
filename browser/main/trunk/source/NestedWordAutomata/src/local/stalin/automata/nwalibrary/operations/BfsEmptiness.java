package local.stalin.automata.nwalibrary.operations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.automata.nwalibrary.State;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;


/**
 * Check emptiness and obtain an accepting run of a nested word automaton.
 * The algorithm computes a reachability graph. The nodes of the graph describe
 * a configuration of the automaton. They are represented by state pairs 
 * (state,stateK) where state is the "current state" in the reachability
 * analysis of the automaton, stateK is the last state before the last call
 * transition. If we consider the automaton as a machine with a stack, stateK
 * is the topmost element of the stack.
 * The edges of the reachability graph are labeled with runs of length two or
 * summary.
 * The reachability graph is obtained by traversing the automaton in a BFS 
 * manner. 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */

public class BfsEmptiness<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * INestedWordAutomaton for which we check emptiness.
	 */
	INestedWordAutomaton<S,C> m_nwa;
	
	/**
	 * Pairs of states visited, but possibly not processed, so far.
	 */
	private final Map<IState<S,C>,Set<IState<S,C>>> m_visitedPairs = 
		new HashMap<IState<S,C>,Set<IState<S,C>>>();
	
	/**
	 * Queue of states that have to be processed and have been visited while
	 * processing a internal transition, a return transition or a computed 
	 * summary
	 */
	private final LinkedList<IState<S,C>[]> m_queue =
		new LinkedList<IState<S,C>[]>();

		
	/**
	 * Queue of states that have to be processed and have been visited while
	 * processing a call transition.
	 */
	private final LinkedList<IState<S,C>[]> m_queueCall =
			new LinkedList<IState<S,C>[]>();

	/**
	 * Assigns to a pair of states (state,stateK) the run of length 2 that is
	 * labeled to the incoming edge of (state,stateK) in the reachability graph.
	 * The symbol of the run has to be an internal symbol. The predecessor of
	 * (state,stateK) in the reachability graph is (pred,predK), where pred is 
	 * the first state of the run and predK is stateK.  
	 */
	private final Map<IState<S,C>,
	                  Map<IState<S,C>,NestedRun<S,C>>> m_internalSubRun =
		new HashMap<IState<S,C>,Map<IState<S,C>,NestedRun<S,C>>>();
	
	/**
	 * Assigns to a triple of states (state,stateK,predK) the run of length 2
	 * that is labeled to the incoming edge of the state pair (state,stateK)
	 * in the reachability graph. The symbol of the run has to be a call symbol.
	 * The predecessor of (state,stateK) in the reachability graph is 
	 * (pred,predK), where pred is stateK.  
	 */
	private final Map<IState<S,C>,
	                  Map<IState<S,C>,
	                      Map<IState<S,C>,NestedRun<S,C>>>> m_callSubRun =
		new HashMap<IState<S,C>,
		            Map<IState<S,C>,Map<IState<S,C>,NestedRun<S,C>>>>();
	
	/**
	 * Assigns to a pair of states (state,stateK) a state predK. predK is the
	 * second component of the state pair (pred,predK) for which (state,stateK)
	 * was added to the reachability graph (for the first time).  
	 */
	private final Map<IState<S,C>,Map<IState<S,C>,IState<S,C>>> m_callFirst =
		new HashMap<IState<S,C>,Map<IState<S,C>,IState<S,C>>>();


	/**
	 * Assigns to a pair of states (state,stateK) the run of length 2 that is
	 * labeled to the incoming edge of (state,stateK) in the reachability graph.
	 * The symbol of the run has to be a return symbol. The predecessor of
	 * (state,stateK) in the reachability graph is (pred,predK), where pred is 
	 * the first state of the run. predK can be obtained from m_returnPredStateK  
	 */
	private final Map<IState<S,C>,
				      Map<IState<S,C>,NestedRun<S,C>>> m_returnSubRun = 
		new HashMap<IState<S,C>,Map<IState<S,C>,NestedRun<S,C>>>();
	
	/**
	 * Assigns to a pair of states (state,stateK) a state predK. predK is the
	 * second component of the predecessor (pred,predK) of (state,stateK) in the
	 * reachability graph.
	 */
	private final Map<IState<S,C>,
	                  Map<IState<S,C>,IState<S,C>>> m_returnPredStateK = 
		new HashMap<IState<S,C>,Map<IState<S,C>,IState<S,C>>>();
	
	
	
	/**
	 * If a triple (state,succ,returnPred) is contained in this map, a summary
	 * from state to succ has been discovered and returnPred is the predecessor
	 * of the return transition of this summary.
	 */
	private final Map<IState<S,C>,
	                  Map<IState<S,C>,IState<S,C>>> m_summaryReturnPred =
		new HashMap<IState<S,C>,Map<IState<S,C>,IState<S,C>>>();

	/**
	 * If a triple (state,succ,symbol) is contained in this map, a summary
	 * from state to succ has been discovered and symbol is the label of the
	 * return transition of this summary.
	 */
	private final Map<IState<S,C>,
	                  Map<IState<S,C>,S>> m_summaryReturnSymbol =
		new HashMap<IState<S,C>,Map<IState<S,C>,S>>();


	
	/**
	 * Second Element of the initial state pair. This state indicates that
	 * nothing is on the stack of the automaton, in other words while processing
	 * we have taken the same number of calls and returns.
	 */
	IState<S,C> dummyEmptyStackState = new State<S,C>(false, null);
	

	/**
	 * Stack for the constructing a run if non-emptiness was detected. Contains
	 * an element for every return that was processed and to corresponding call
	 * was processed yet.
	 * Corresponds to the stack-of-returned-elements-that-have-not-been-called
	 * of the automaton but all elements are shifted by one.   
	 */
	Stack<IState<S,C>> m_reconstructionStack = new Stack<IState<S,C>>();
	
	
	public BfsEmptiness(INestedWordAutomaton<S,C> nwa) {
		m_nwa = nwa;
	}
	
	
	/**
	 * Enqueue a state pair that has been discovered by taking an internal
	 * transition, a return transition or a summary. Mark the state pair as
	 * visited afterwards. 
	 */
	private void enqueueAndMarkVisited(IState<S,C> state,
			                           IState<S,C> stateK) {
		IState[] pair = { state, stateK };
		m_queue.addLast(pair);
		markVisited(state, stateK);
	}
	
	
	/**
	 * Enqueue a state pair that has been discovered by taking a call
	 * transition. Mark the state pair as visited afterwards. 
	 */
	private void enqueueAndMarkVisitedCall(IState<S,C> state,
									       IState<S,C> callPred) {
		IState[] pair = { state, callPred };
		m_queueCall.addLast(pair);
		markVisited(state, callPred);
	}
	
	
//  The following implementation of dequeue is faster but leads to unsound
//	results. See BugBfsEmptinessLowPriorityCallQueue.fat for details.
//  Alternative workaround (where we may still use the low priority call queue):
//  When final state is reached, process the whole call queue before
//  computation of accepting run.
//	/**
//	 * Dequeue a state pair. If available take a state pair that has been
//	 * discovered by taking an internal transition, a return transition or a
//	 * summary. If not take a state pair that has been discovered by taking a
//	 * call transition.
//	 */
//	private IState<S,C>[] dequeue() {
//		if (!m_queue.isEmpty()) {
//			return m_queue.removeFirst();
//		}
//		else {
//			return m_queueCall.removeFirst();
//		}
//	}
	/**
	 * Dequeue a state pair. If available take a state pair that has been
	 * discovered by taking a
	 * call transition. If not take a state pair that has been discovered by 
	 * taking an internal transition, a return transition or a
	 * summary.
	 */
	private IState<S,C>[] dequeue() {
		if (!m_queueCall.isEmpty()) {
			return m_queueCall.removeFirst();
		}
		else {
			return m_queue.removeFirst();
		}
	}
	
	/**
	 * Is the queue (is internally represented by two queues) empty? 
	 */
	private boolean isQueueEmpty() {
		return m_queue.isEmpty() && m_queueCall.isEmpty();
	}
	
	
	/**
	 * Mark a state pair a visited. 
	 */
	private void markVisited(IState<S,C> state, IState<S,C> stateK) {
		Set<IState<S,C>> callPreds = m_visitedPairs.get(state);
		if (callPreds == null) {
			callPreds = new HashSet<IState<S,C>>();
			m_visitedPairs.put(state, callPreds);
		}
		callPreds.add(stateK);
	}
	
	
	/**
	 * Was the state pair (state,stateK) already visited?
	 */
	private boolean wasVisited(IState<S,C> state, IState<S,C> stateK) {
		Set<IState<S,C>> callPreds = m_visitedPairs.get(state);
		if (callPreds == null) {
			return false;
		}
		else {
			return callPreds.contains(stateK);
		}
	}
	

	
	/**
	 * Get an accepting run of the automaton passed to the constructor. Return
	 * null if the automaton does not accept any nested word.
	 */
	public NestedRun<S,C> getAcceptingRun() {
		for (IState<S,C> state : m_nwa.getInitialStates()) {
			enqueueAndMarkVisited(state, dummyEmptyStackState);
		}
	
		while (!isQueueEmpty()) {
			IState<S,C>[] pair = dequeue();
			IState<S,C> state = pair[0];
			IState<S,C> stateK = pair[1];
			
			if (state.isFinal()) {
				return constructRun(state, stateK);
			}
			
			processSummaries(state,stateK);
			
			for (S symbol : state.getSymbolsInternal()) {
				for (IState<S,C> succ : state.getInternalSucc(symbol)) {
					if(!wasVisited(succ, stateK)) {
						addRunInformationInternal(
											succ,stateK,symbol,state,stateK);
						enqueueAndMarkVisited(succ, stateK);
					}
					
				}
			}
			for (S symbol : state.getSymbolsCall()) {
				for (IState<S,C> succ : state.getCallSucc(symbol)) {
					//add these information even in already visited
//remove this line					addCallStatesOfCallState(state, stateK);
					addRunInformationCall(succ, state, symbol, state, stateK);
					if(!wasVisited(succ, state)) {
						enqueueAndMarkVisitedCall(succ, state);
					}
				}
			}
			for (S symbol : state.getSymbolsReturn()) {
				for (IState<S,C> succ : state.getReturnSucc(stateK,symbol)) {
					for (IState<S,C> stateKK : 
											getCallStatesOfCallState(stateK) ) {
						addSummary(stateK, succ, state, symbol);
						if(!wasVisited(succ, stateKK)) {
							enqueueAndMarkVisited(succ, stateKK);
							addRunInformationReturn(
										succ, stateKK, symbol, state, stateK);
						}
						
					}
				}
			}
		}
		return null;
	}
	
	/**
	 * Compute successor state pairs (succ,succK) of the state pair
	 * (state,stateK) under an already discovered summary in the reachability
	 * graph.
	 * succK is stateK. For adding run information for (succ,succK) information
	 * about the summary is fetched. 
	 */
	private void processSummaries(IState<S,C> state, IState<S,C> stateK) {
		if (m_summaryReturnPred.containsKey(state)) {
			assert(m_summaryReturnSymbol.containsKey(state));
			Map<IState<S,C>,IState<S,C>> succ2ReturnPred = 
						m_summaryReturnPred.get(state);
			Map<IState<S,C>,S> succ2ReturnSymbol = 
						m_summaryReturnSymbol.get(state);
			for (IState<S,C> succ : succ2ReturnPred.keySet()) {
				assert(succ2ReturnSymbol.containsKey(succ));
				IState<S,C> returnPred = succ2ReturnPred.get(succ);
				S symbol = succ2ReturnSymbol.get(succ);
				if(!wasVisited(succ, stateK)) {
					enqueueAndMarkVisited(succ, stateK);
					addRunInformationReturn(
									succ, stateK, symbol, returnPred, state);
				}
			}
			
		}
		
	}

	
	/**
	 * Store for a state pair (succ,succK) in the reachability graph information
	 * about the predecessor (state,stateK) under an internal transition and a
	 * run of length two from state to succ.
	 */
	private void addRunInformationInternal(IState<S,C> succ,
			IState<S,C> succK,
			S symbol,
			IState<S,C> state,
			IState<S,C> stateK) {
		Map<IState<S,C>, NestedRun<S,C>> succK2run = 
													m_internalSubRun.get(succ);
		if (succK2run == null) {
			succK2run = new HashMap<IState<S,C>, NestedRun<S,C>>();
			m_internalSubRun.put(succ, succK2run);
		}
		assert(succK2run.get(succK) == null);
		NestedRun<S,C> run = new NestedRun<S,C>(
							state, symbol, NestedWord.INTERNAL_POSITION, succ);
		succK2run.put(succK, run);
	}
	
	/**
	 * Store for a state pair (succ,succK) in the reachability graph information
	 * about the predecessor (state,stateK) under a call transition and a
	 * run of length two from state to succ.
	 * If (succ,succK) was visited for the first time, store also stateK in
	 * m_callFirst.
	 */
	private void addRunInformationCall(IState<S,C> succ,
			IState<S,C> succK,
			S symbol,
			IState<S,C> state,
			IState<S,C> stateK) {
//		s_Logger.debug("Call SubrunInformation: From ("+succ+","+succK+
//			") can go to ("+state+","+stateK+")");
		assert(state == succK);
		Map<IState<S,C>, Map<IState<S,C>, NestedRun<S,C>>> succK2stateK2Run = 
				m_callSubRun.get(succ);
		Map<IState<S,C>, IState<S,C>> succK2FirstStateK = 
				m_callFirst.get(succ);
		if (succK2stateK2Run == null) {
			assert(succK2stateK2Run == null);
			succK2stateK2Run = 
				new HashMap<IState<S,C>, Map<IState<S,C>, NestedRun<S,C>>>();
			m_callSubRun.put(succ,succK2stateK2Run);
			succK2FirstStateK = new HashMap<IState<S,C>, IState<S,C>>();
			m_callFirst.put(succ, succK2FirstStateK);
		}
		if (!succK2FirstStateK.containsKey(succK)) {
			succK2FirstStateK.put(succK, stateK);
		}
		Map<IState<S,C>, NestedRun<S,C>> stateK2Run = 
				succK2stateK2Run.get(succK);
		if (stateK2Run == null) {
			stateK2Run = new HashMap<IState<S,C>, NestedRun<S,C>>();
			succK2stateK2Run.put(succK,stateK2Run);
		}
//		The following assertion is wrong, there can be a two different call
//		transitions from stateK to state. (But in this case we always want to
//		take the one that was first discovered.)
//		assert(!stateK2Run.containsKey(stateK));
		NestedRun<S,C> run = 
			new NestedRun<S,C>(state, symbol, NestedWord.PLUS_INFINITY, succ);
		stateK2Run.put(stateK, run);
	}
	
	
	/**
	 * Store for a state pair (succ,succK) in the reachability graph information
	 * about the predecessor (state,stateK) under a return transition and a
	 * run of length two from state to succ.
	 * Store also succK to m_returnPredStateK.
	 */
	private void addRunInformationReturn(IState<S,C> succ,
			IState<S,C> succK,
			S symbol,
			IState<S,C> state,
			IState<S,C> stateK) {
		Map<IState<S,C>, NestedRun<S,C>> succK2SubRun = 
									m_returnSubRun.get(succ);
		Map<IState<S,C>, IState<S,C>> succK2PredStateK = 
									m_returnPredStateK.get(succ);
		if (succK2SubRun == null) {
			assert(succK2PredStateK == null);
			succK2SubRun = new HashMap<IState<S,C>, NestedRun<S,C>>();
			m_returnSubRun.put(succ,succK2SubRun);
			succK2PredStateK = new HashMap<IState<S,C>, IState<S,C>>();
			m_returnPredStateK.put(succ, succK2PredStateK);
		}
		assert(!succK2SubRun.containsKey(succK));
		assert(!succK2PredStateK.containsKey(succK));
		NestedRun<S,C> run = 
			new NestedRun<S,C>(state, symbol, NestedWord.MINUS_INFINITY, succ);
		succK2SubRun.put(succK, run);
		succK2PredStateK.put(succK, stateK);
	}
	

	/**
	 * Get all states which occur as the second component of a state pair
	 * (callState,*) in the reachability graph, where the first component is
	 * callState. 
	 */
	private Set<IState<S,C>> getCallStatesOfCallState(IState<S,C> callState) {
		Set<IState<S,C>> callStatesOfCallStates = m_visitedPairs.get(callState);
		if (callStatesOfCallStates == null) {
			return new HashSet<IState<S,C>>(0);
		}
		else {
			return callStatesOfCallStates;
		}
	}
	
//	private void addCallStatesOfCallState(IState<S,C> callState,
//			                              IState<S,C> callStateOfCallState) {
//		Set<IState<S,C>> callStatesOfCallStates = 
//							m_CallStatesOfCallState.get(callState);
//		if (callStatesOfCallStates == null) {
//			callStatesOfCallStates = new HashSet<IState<S,C>>();
//			m_CallStatesOfCallState.put(callState,callStatesOfCallStates);
//		}
//		callStatesOfCallStates.add(callStateOfCallState);
//	}

	
	/**
	 * Store information about a discovered summary.
	 */
	private void addSummary(IState<S,C> stateBeforeCall,
							IState<S,C> stateAfterReturn,
							IState<S,C> stateBeforeReturn,
							S returnSymbol) {
		Map<IState<S,C>,IState<S,C>> succ2ReturnPred = 
			m_summaryReturnPred.get(stateBeforeCall);
		Map<IState<S,C>,S> succ2ReturnSymbol = 
			m_summaryReturnSymbol.get(stateBeforeCall);
		if (succ2ReturnPred == null) {
			assert(succ2ReturnSymbol == null);
			succ2ReturnPred = new HashMap<IState<S,C>,IState<S,C>>();
			m_summaryReturnPred.put(stateBeforeCall, succ2ReturnPred);
			succ2ReturnSymbol = new HashMap<IState<S,C>,S>();
			m_summaryReturnSymbol.put(stateBeforeCall, succ2ReturnSymbol);
			
		}
		//update only if there is not already an entry
		if (!succ2ReturnPred.containsKey(stateAfterReturn)) {
			succ2ReturnPred.put(stateAfterReturn,stateBeforeReturn);
			assert (!succ2ReturnSymbol.containsKey(stateAfterReturn));
			succ2ReturnSymbol.put(stateAfterReturn, returnSymbol);
		}
	}
	
	
	
	
	/**
	 * Construct a run for a discovered final state in the reachability
	 * analysis. The run is constructed backwards using the information of
	 * predecessors in the reachability graph and the corresponding runs of
	 * length two.
	 */
	private NestedRun<S,C> constructRun(IState<S,C> state, IState<S,C> stateK) {
//		s_Logger.debug("Reconstruction from " + state + " " + stateK);
		if ( m_nwa.getInitialStates().contains(state) &&
				m_reconstructionStack.isEmpty()) {
			return new NestedRun<S,C>(state);
		}
		else {
			NestedRun<S,C> run;
			IState<S,C> pred;
			IState<S,C> predK;
			
			Map<IState<S,C>, NestedRun<S,C>> k2InternalMap = 
				m_internalSubRun.get(state);
			if (k2InternalMap != null) {
				run = k2InternalMap.get(stateK);
				if (run != null) {
					pred = run.getStateAtPosition(0);
					predK = stateK;
					return constructRun(pred, predK).concatenate(run);
				}
			}
			
			Map<IState<S,C>, Map<IState<S,C>, NestedRun<S,C>>> k2CallMap = 
				m_callSubRun.get(state);
			if (k2CallMap != null) {
				Map<IState<S,C>, NestedRun<S,C>> callMap = 
					k2CallMap.get(stateK);
				if (callMap != null) {
					if (m_reconstructionStack.isEmpty()) {
						predK = m_callFirst.get(state).get(stateK);
						run = callMap.get(predK);
						pred = run.getStateAtPosition(0);
						return constructRun(pred, predK).concatenate(run);
					}
					else {
						IState<S,C> predKcandidate = 
							m_reconstructionStack.peek();
						if (callMap.containsKey(predKcandidate)) {
							run = callMap.get(predKcandidate);
							pred = run.getStateAtPosition(0);
							predK = predKcandidate;
							m_reconstructionStack.pop();
//							s_Logger.debug("Removed from reconstruction Stack: "
//								+ predKcandidate);
							return constructRun(pred, predK).concatenate(run);
						}
					}
				}
			}
			
			Map<IState<S,C>, NestedRun<S,C>> succK2SubRun = 
					m_returnSubRun.get(state);
			Map<IState<S,C>, IState<S,C>> succK2PredStateK = 
					m_returnPredStateK.get(state);
			if (succK2SubRun != null) {
				assert (succK2PredStateK != null);
				run = succK2SubRun.get(stateK);
				predK = succK2PredStateK.get(stateK);
				if (run != null) {
					pred = run.getStateAtPosition(0);
					m_reconstructionStack.push(stateK);
//					s_Logger.debug("Put on the reconstruction Stack: "+ stateK);
					return constructRun(pred, predK).concatenate(run);
				}
			}
			s_Logger.warn("No Run ending in pair "+state+ "  "+ stateK + 
					" with reconstructionStack" + m_reconstructionStack);
			throw new AssertionError();
		}
			
	}
	
}
