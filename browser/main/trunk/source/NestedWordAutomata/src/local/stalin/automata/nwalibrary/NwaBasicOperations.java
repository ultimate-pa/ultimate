package local.stalin.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentLinkedQueue;

import local.stalin.automata.Activator;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;



public class NwaBasicOperations<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private NestedWordAutomaton<S,C> nwa;




	public NwaBasicOperations(NestedWordAutomaton<S,C> nwa) {
		this.nwa = nwa;
	}

	
	
	public boolean accepts(NestedWord<S> nw) 
	{
		Stack<IState<S,C>> stack = new Stack<IState<S,C>>();
		Collection<IState<S,C>> initials = nwa.getInitialStates();
		for(IState<S,C> state : initials)
		{
			if(RecursiveAcceptsExecution(nw, state, 0, stack))
			{
				return true;
			}
		}
		return false;	
	}
	
	/**
	 * @author Daniel Christiany
	 * RecursiveAcceptsExecution goes recursively through the nested word and determines if a Nested Word is accepted
	 * @param nw - the nested word of which we want to determine if it is accepted by given NWA
	 * @param current - the State the execution is currently in
	 * @param position - the position of the Nested Words Symbol which is to be processed in this run
	 * @param stack - the stack containing the states, from which there was a call transition
	 * @return whether NestedWord is accepted by this NWA or not
	 */
	private boolean RecursiveAcceptsExecution(NestedWord<S> nw, IState<S,C> current, int position, Stack<IState<S,C>> stack)
	{
		//if we handled the entire word, the only thing left is determining if the final state is accepting
		if(position == nw.length())
		{
			return current.isFinal();
		}
		//if we haven't handled the entire word, handle the current symbol
		else
		{
			S symbol = nw.getSymbolAt(position);
			if(nw.isCallPosition(position))
			{
				if(nwa.getCallAlphabet().contains(symbol))
				{
					stack.push(current);
					for(IState<S,C> successor : current.getCallSucc(symbol))
					{
						if(RecursiveAcceptsExecution(nw, successor, position+1, stack))
							return true;
					}
					stack.pop();
				}
				else
				{
					//TODO: We Dont have a content? WTF?
					//s_Logger.error("Symbol " + symbol + " is a call symbol in Nested Word " + nw + " but is not part of the NWAs call alphabet whose content is " + content);
					return false;
				}
			}
			else if(nw.isInternalPosition(position))
			{
				if(nwa.getInternalAlphabet().contains(symbol))
				{
					for(IState<S,C> successor : current.getInternalSucc(symbol))
					{
						if(RecursiveAcceptsExecution(nw, successor, position+1, stack))
							return true;
					}
				}
				else
				{
					//TODO: We Dont have a content? WTF?
					//s_Logger.error("Symbol " + symbol + " is an internal symbol in Nested Word " + nw + " but is not part of the NWAs call alphabet whose content is " + content);
					return false;
				}
			}
			else if(nw.isReturnPosition(position))
			{
				if(nwa.getReturnAlphabet().contains(symbol))
				{
					if(!stack.isEmpty())
					{
						IState<S,C> top = stack.pop();
						for(IState<S,C> successor : current.getReturnSucc(top, symbol))
						{
							if(RecursiveAcceptsExecution(nw, successor, position+1, stack))
								return true;
						}
						stack.push(top);
					}
					else
						return false;
				}
				else
				{
					//TODO: We Dont have a content? WTF?
					//s_Logger.error("Symbol " + symbol + " is a return symbol in Nested Word " + nw + " but is not part of the NWAs call alphabet whose content is " + content);
					return false;
				}
			}
			return false;
		}
	}
	
	
	
	
	
	/**
	 * @author Jan Leike 
	 * @author Marcus Zeiger
	 */
	public INestedWordAutomaton<S,C> determinizeJM() {
		/*
		 * This is the implementation as described in
		 * "Adding Nesting Structure to Words" by Rajeev Alur and P. Madhusudan LNCS 4036
		 * Section 3.2 (page 6)
		 * 
		 * A new deterministic state is of type
		 * "Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>".
		 * 
		 * Runtime: O(2^(s^2)); s being the number of states
		 */
		
		if (nwa.isDeterministic())
			return new NestedWordAutomaton<S,C>(nwa);
		
		NestedWordAutomaton<S,C> result = new NestedWordAutomaton<S,C>(
				nwa.getInternalAlphabet(), nwa.getCallAlphabet(), nwa.getReturnAlphabet(), nwa.getContentFactory());
		
		// Initialize the state queue: This queue holds the states which are to be deteminized
		Queue<DeterminizedState> stateQueue = new ConcurrentLinkedQueue<DeterminizedState>();
		
		// Create a new DeterminizationMap to store all state equivalences
		DeterminizationMap detMap = new DeterminizationMap(nwa, result, stateQueue);
		
		// Create a new initial state
		Set<Pair<IState<S,C>, IState<S,C>>> initState
			= new TreeSet<Pair<IState<S,C>, IState<S,C>>>();
		for (IState<S,C> state : nwa.initialStates)
			initState.add(new Pair<IState<S,C>, IState<S,C>>(state, state));
		DeterminizedState dInitState = detMap.get(initState);
		result.initialStates.add(dInitState.detState);
		
		// Start by queuing the first state
		stateQueue.add(dInitState);
		
		while (!stateQueue.isEmpty()) {
			// Get the new state that will be determinized
			DeterminizedState dState = stateQueue.poll();
			
			// Determinize all internal transitions
			// ------------------------------------
			
			// Find transition symbols
			Collection<S> internalSymbols = new TreeSet<S>(CompareByHash.instance);
			for (Pair<IState<S,C>, IState<S,C>> pair : dState.pairSet)
				internalSymbols.addAll(pair.snd.getSymbolsInternal());
			assert nwa.internalAlphabet.containsAll(internalSymbols);
			
			// Do transitions for all state pairs in the set
			for (S symbol : internalSymbols) {
				Set<Pair<IState<S,C>, IState<S,C>>> succState
					= new TreeSet<Pair<IState<S,C>, IState<S,C>>>();
				
				// For each possible transition of each state add the resulting state to the succState
				for (Pair<IState<S,C>, IState<S,C>> pair : dState.pairSet)
					for (IState<S,C> nextState : pair.snd.getInternalSucc(symbol))
						succState.add(new Pair<IState<S,C>, IState<S,C>>(pair.fst, nextState));

				if (!succState.isEmpty())
					result.addInternalTransition(dState.detState, symbol, detMap.get(succState).detState);
			}
			
			// Determinize all call transitions
			// --------------------------------
			
			// Find transition symbols
			Collection<S> callSymbols = new TreeSet<S>(CompareByHash.instance);
			for (Pair<IState<S,C>, IState<S,C>> pair : dState.pairSet)
				callSymbols.addAll(pair.snd.getSymbolsCall());
			assert nwa.callAlphabet.containsAll(callSymbols);
			
			// Do transitions for all state pairs in the set
			for (S symbol : callSymbols) {
				Set<Pair<IState<S,C>, IState<S,C>>> succState
					= new TreeSet<Pair<IState<S,C>, IState<S,C>>>();
				
				// For each possible transition of each state add the resulting state to the succState
				for (Pair<IState<S,C>, IState<S,C>> pair : dState.pairSet)
					for (IState<S,C> nextState : pair.snd.getCallSucc(symbol))
						succState.add(new Pair<IState<S,C>, IState<S,C>>(pair.snd, nextState));
				
				if (!succState.isEmpty())
					result.addCallTransition(dState.detState, symbol, detMap.get(succState).detState);
			}
			
			// Determinize all return transitions
			// --------------------------------
			
			// Find transition symbols
			Collection<S> returnSymbols = new TreeSet<S>(CompareByHash.instance);
			for (Pair<IState<S,C>, IState<S,C>> pair : dState.pairSet)
				returnSymbols.addAll(pair.snd.getSymbolsReturn());
			assert nwa.returnAlphabet.containsAll(returnSymbols);
			
			/*
			 * Insert new return transition (S, S', a, T) where
			 * T = {(q, q') | (q1, q2) ∈ S, (q, q1) ∈ S', (q2, q1, a, q') ∈ δr } for every S'
			 */
			
			// Create transitions for all existing states
			for (S symbol : returnSymbols) {
				Set<DeterminizedState> detMapValues = new TreeSet<DeterminizedState>(CompareByHash.instance);
				detMapValues.addAll(detMap.getAll());
				for (DeterminizedState dOtherState : detMapValues) {
					// Only consider this state if it has call transitions
					if (dOtherState.detState.getSymbolsCall().isEmpty())
						continue;
					
					Set<Pair<IState<S,C>, IState<S,C>>> succState
						= new TreeSet<Pair<IState<S,C>, IState<S,C>>>();
					
					for (Pair<IState<S,C>, IState<S,C>> pair : dState.pairSet) {
						// Transition available?
						if (pair.snd.getReturnSucc(pair.fst, symbol).isEmpty())
							continue;
						
						for (Pair<IState<S,C>, IState<S,C>> otherPair : dOtherState.pairSet) {
							if (otherPair.snd != pair.fst)
								continue;
							
							Collection<IState<S,C>> returns = pair.snd.getReturnSucc(pair.fst, symbol);
							if (!returns.isEmpty()) {
								for (IState<S,C> retState : returns)
									succState.add(new Pair<IState<S,C>, IState<S,C>>(otherPair.fst, retState));
							}
						}
					}
					
					if (!succState.isEmpty())
						result.addReturnTransition(dState.detState, dOtherState.detState, symbol, detMap.get(succState).detState);
				}
			}
			
			// Check for return transitions using dState as predecessor
			// --------------------------------
			
			// Does dState have a call transition?
			if (!dState.detState.getSymbolsCall().isEmpty())
				// Do the same as above with S and S' switched
				for (S symbol : nwa.returnAlphabet){
					Set<DeterminizedState> detMapValues = new TreeSet<DeterminizedState>(CompareByHash.instance);
					detMapValues.addAll(detMap.getAll());
					for (DeterminizedState dOtherState : detMapValues) {
						Set<Pair<IState<S,C>, IState<S,C>>> succState
							= new TreeSet<Pair<IState<S,C>, IState<S,C>>>();
						
						for (Pair<IState<S,C>, IState<S,C>> otherPair : dOtherState.pairSet) {
							// Transition available?
							if (otherPair.snd.getReturnSucc(otherPair.fst, symbol).isEmpty())
								continue;
							
							for (Pair<IState<S,C>, IState<S,C>> pair : dState.pairSet) {
								if (pair.snd != otherPair.fst)
									continue;
								
								Collection<IState<S,C>> returns = otherPair.snd.getReturnSucc(otherPair.fst, symbol);
								if (!returns.isEmpty()) {
									for (IState<S,C> retState : returns)
										succState.add(new Pair<IState<S,C>, IState<S,C>>(pair.fst, retState));
								}
							}
						}
						
						if (!succState.isEmpty())
							result.addReturnTransition(dOtherState.detState, dState.detState, symbol, detMap.get(succState).detState);
					}
				}
		}
		
		assert result.isDeterministic();
		s_Logger.debug("The non-deterministic NWA has "+nwa.states.size()+" states. The resulting NWA has "
				+ result.states.size()+ " states" );
		assert result.states.size() <= Math.pow(2, Math.pow(nwa.states.size(), 2)): "size problem";
		return result;
	}
		
	/** 
	 * Data structure to store the determinized states for this.determinize()
	 */
	private class DeterminizationMap {
		Map<Set<Pair<IState<S,C>, IState<S,C>>>, DeterminizedState> data;
		
		// These need to be accessed at new state creation
		NestedWordAutomaton<S,C> old_nwa;
		NestedWordAutomaton<S,C> new_nwa;
		Queue<DeterminizedState> stateQueue;
		
		// Constructor initializes the data structure
		public DeterminizationMap(NestedWordAutomaton<S,C> old_nwa, NestedWordAutomaton<S,C> new_nwa, Queue<DeterminizedState> stateQueue) {
			this.data = new TreeMap<Set<Pair<IState<S,C>, IState<S,C>>>, DeterminizedState>(CompareByHash.instance);
			this.old_nwa = old_nwa;
			this.new_nwa = new_nwa;
			this.stateQueue = stateQueue;
		}
		
		/**
		 * @param a set of pairs which represent a state
		 * @return the equivalent deterministic state
		 */
		public DeterminizedState get(Set<Pair<IState<S,C>, IState<S,C>>> state) {
			// Check if this state was already created at some point
			if (data.containsKey(state)) {
				return data.get(state);
			} else {
				// Create new content
				Collection<Pair<C,C>> cPairList = new ArrayList<Pair<C,C>>();
				for (Pair<IState<S,C>, IState<S,C>> pair : state)
					cPairList.add(new Pair<C,C>(pair.fst.getContent(), pair.snd.getContent()));
				C content = nwa.m_contentFactory.createContentOnDeterminization(cPairList);
				
				// Check if state is final
				boolean isFinal = false;
				for (Pair<IState<S,C>, IState<S,C>> pair : state)
					if (pair.snd.isFinal()) {
						isFinal = true;
						break;
					}
				
				IState<S,C> newState = new_nwa.addState(false, isFinal, content);
				DeterminizedState dState = new DeterminizedState(state, newState);
				
				// Store the new dState in data to find it later
				this.data.put(state, dState);
				
				// Queue new dState!
				this.stateQueue.add(dState);
				
				return dState;
			}
		}
		
		/**
		 * @return a Collection of all determinized states 
		 */
		public Collection<DeterminizedState> getAll() {
			return this.data.values();
		}
	}
	
	// This is just a shorter way to write Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>
	// The IState is stored for performance reasons
	private class DeterminizedState {
		public DeterminizedState(Set<Pair<IState<S,C>, IState<S,C>>> pairSet, IState<S,C> detState) {
			assert pairSet != null;
			assert detState != null;
			this.pairSet = pairSet;
			this.detState = detState;
		}
		
		Set<Pair<IState<S,C>, IState<S,C>>> pairSet;
		IState<S,C> detState; // cached!
	}	
	
	
	

	
	
	
	
	
	
	
	
	
	/**
	 * Implementation of intersection that constructes the complete product.
	 * @author Jan Leike 
	 */
	public INestedWordAutomaton<S,C> intersectFullProduct(INestedWordAutomaton<S,C> nwa2) {
		/*
		 * Create the automaton that accepts exactly the nested words that are accepted by
		 * the two given automata.
		 * 
		 * This algorithm uses a product set construction.
		 * 
		 * Runtime: O(a*s^2); s being the number of states and a the alphabet size
		 */
		
		if (nwa2 == null)
			throw new NullPointerException();
		
		// Intersect alphabets
		//FIXME: Case where Symbol is compareable
		Set<S> newInternals = new TreeSet<S>(CompareByHash.instance);
		newInternals.addAll(nwa.internalAlphabet);
		newInternals.retainAll(nwa2.getInternalAlphabet());
		Set<S> newCalls = new TreeSet<S>(CompareByHash.instance);
		newCalls.addAll(nwa.callAlphabet);
		newCalls.retainAll(nwa2.getCallAlphabet());
		Set<S> newReturns = new TreeSet<S>(CompareByHash.instance);
		newReturns.addAll(nwa.returnAlphabet);
		newReturns.retainAll(nwa2.getReturnAlphabet());
		
		
		INestedWordAutomaton<S,C> result = new NestedWordAutomaton<S,C>(newInternals, newCalls, newReturns, nwa.m_contentFactory);
		Map<IState<S,C>, Map<IState<S,C>, State<S,C>>> stateMap
			= new HashMap<IState<S,C>, Map<IState<S,C>, State<S,C>>>();
		
		// Create new states (product set of this.states and nwa.states)
		for (IState<S,C> state1 : nwa.states) {
			Map<IState<S,C>, State<S,C>> map2
				= new HashMap<IState<S,C>, State<S,C>>();
			for (IState<S,C> state2 : nwa2.getAllStates()) {
				C newContent = nwa.m_contentFactory.createContentOnIntersection(state1.getContent(), state2.getContent());
				boolean isFinal = state1.isFinal() && state2.isFinal();
				boolean isInitial = nwa.initialStates.contains(state1) && nwa2.getInitialStates().contains(state2);
				State<S,C> newState = (State<S,C>)result.addState(isInitial, isFinal, newContent);
				map2.put(state2, newState);
			}
			stateMap.put(state1, map2);
		}
		
		// Insert transitions
		for (IState<S,C> state1 : nwa.states) {
			for (IState<S,C> state2 : nwa2.getAllStates()) {
				State<S,C> newState = stateMap.get(state1).get(state2);
				
				// Create internal transitions 
				Collection<S> internalTransitionSymbols = new ArrayList<S>();
				for (S symbol : state1.getSymbolsInternal()) {
					assert nwa.internalAlphabet.contains(symbol);
					if (state2.getSymbolsInternal().contains(symbol))
						internalTransitionSymbols.add(symbol);
				}
				
				for (S symbol : internalTransitionSymbols) {
					Collection<IState<S,C>> succ1 = state1.getInternalSucc(symbol);
					Collection<IState<S,C>> succ2 = state2.getInternalSucc(symbol);
					assert succ1 != null;
					assert succ1.size() > 0;  // internalTransitionSymbols was created this way
					assert succ2 != null;
					assert succ2.size() > 0;  // internalTransitionSymbols was created this way
					for (IState<S,C> succState1 : succ1)
						for (IState<S,C> succState2 : succ2) {
							IState<S,C> succState = stateMap.get(succState1).get(succState2);
							newState.addInternalTransition(symbol, succState);
						}
				}
				
				// Create call transitions
				Collection<S> callTransitionSymbols = new ArrayList<S>();
				for (S symbol : state1.getSymbolsCall()) {
					assert nwa.callAlphabet.contains(symbol);
					if (state2.getSymbolsCall().contains(symbol))
						callTransitionSymbols.add(symbol);
				}
				
				for (S symbol : callTransitionSymbols) {
					Collection<IState<S,C>> succ1 = state1.getCallSucc(symbol);
					Collection<IState<S,C>> succ2 = state2.getCallSucc(symbol);
					assert succ1 != null;
					assert succ1.size() > 0;  // callTransitionSymbols was created this way
					assert succ2 != null;
					assert succ2.size() > 0;  // callTransitionSymbols was created this way
					for (IState<S,C> succState1 : succ1)
						for (IState<S,C> succState2 : succ2) {
							IState<S,C> succState = stateMap.get(succState1).get(succState2);
							newState.addCallTransition(symbol, succState);
						}
				}
				
				// Create return transitions 
				Collection<S> returnTransitionSymbols = new ArrayList<S>();
				for (S symbol : state1.getSymbolsReturn()) {
					assert nwa.returnAlphabet.contains(symbol);
					if (state2.getSymbolsReturn().contains(symbol))
						returnTransitionSymbols.add(symbol);
				}
				
				for (S symbol : returnTransitionSymbols)
					for (IState<S,C> linPred1 : state1.getReturnLinearPred(symbol))
						for (IState<S,C> linPred2 : state2.getReturnLinearPred(symbol)) {
							Collection<IState<S,C>> succ1 = state1.getReturnSucc(linPred1, symbol);
							Collection<IState<S,C>> succ2 = state2.getReturnSucc(linPred2, symbol);
							IState<S,C> linPred = stateMap.get(linPred1).get(linPred2);
							assert succ1 != null;
							assert succ1.size() > 0;  // returnTransitionSymbols was created this way
							assert succ2 != null;
							assert succ2.size() > 0;  // returnTransitionSymbols was created this way
							for (IState<S,C> succState1 : succ1)
								for (IState<S,C> succState2 : succ2) {
									IState<S,C> succState = stateMap.get(succState1).get(succState2);
									newState.addReturnTransition(symbol, linPred, succState);
								}
						}
			}
		}
		
		return result;
	}
	
}
