package local.stalin.automata.nfalibrary;

import java.util.*;
import java.util.concurrent.ConcurrentLinkedQueue;

import local.stalin.automata.nfalibrary.INFAstate;
import local.stalin.automata.nfalibrary.IStateContentFactory;
import local.stalin.automata.nfalibrary.NFArun;
import local.stalin.automata.nfalibrary.StateContent;
import local.stalin.automata.nfalibrary.NFAstate_VM.CompareByHash;

public class NFA_VM<Symbol, Content extends StateContent> {
	Set<Symbol> alphabet;
	public Collection<NFAstate_VM<Symbol,Content>> initialStates;
	IStateContentFactory<Content> contentFactory;
	Collection<NFAstate_VM<Symbol, Content>> allStates;
	
	public NFA_VM(IStateContentFactory<Content> contentFactory) {
		this.alphabet = new TreeSet<Symbol>();
		this.contentFactory = contentFactory;
		this.initialStates = new ArrayList<NFAstate_VM<Symbol, Content>>(); 
		this.allStates = new ArrayList<NFAstate_VM<Symbol, Content>>();
	}

	public NFA_VM(IStateContentFactory<Content> contentFactory, Set<Symbol> alphabet) {
		this.alphabet = alphabet;
		this.contentFactory = contentFactory;
		this.initialStates = new ArrayList<NFAstate_VM<Symbol, Content>>();
		this.allStates = new ArrayList<NFAstate_VM<Symbol, Content>>();
	}
	
	// Copy constructor
	public NFA_VM(NFA_VM<Symbol, Content> automaton) {
		if (automaton == null)
			throw new NullPointerException();
		
		// Copy all states
		Map<NFAstate_VM<Symbol, Content>, NFAstate_VM<Symbol, Content>> stateCopies
			= new HashMap<NFAstate_VM<Symbol, Content>, NFAstate_VM<Symbol, Content>>();
		for (NFAstate_VM<Symbol, Content> state : automaton.allStates) {
			NFAstate_VM<Symbol, Content> newState = new NFAstate_VM<Symbol, Content>(state);
			stateCopies.put(state, newState);
			allStates.add(newState);
			if (automaton.initialStates.contains(state))
				initialStates.add(newState);
		}
		
		// Copy transition functions for each state
		for (NFAstate_VM<Symbol, Content> state : automaton.allStates) {
			NFAstate_VM<Symbol, Content> newState = stateCopies.get(state);
			
			// Copy the transition for each symbol
			for (Map.Entry<Symbol, Collection<NFAstate_VM<Symbol, Content>>> transition : state.outTransitions.entrySet())
				for (NFAstate_VM<Symbol, Content> nextState : transition.getValue())
					newState.addTransition(transition.getKey(), stateCopies.get(nextState));
		}
	}
	
	// Get the accepting states
	public Collection<NFAstate_VM<Symbol, Content>> getAcceptingStates() {
		Collection<NFAstate_VM<Symbol, Content>> result = new TreeSet<NFAstate_VM<Symbol, Content>>();
		for (NFAstate_VM<Symbol, Content> state : allStates) {
			if (state.isAccepting)
				result.add(state);
		}
		return result;
	}
	
	// Create a new state
	public NFAstate_VM<Symbol, Content> addState(boolean isInitial, boolean isAccepting, Content content) {
		NFAstate_VM<Symbol, Content> newState = new NFAstate_VM<Symbol, Content>();
		this.allStates.add(newState);
		
		if (isInitial)
			this.initialStates.add(newState);
		newState.isAccepting = isAccepting;
		newState.content = content;
		
		return newState;
	}
	
	// Add a new transition to a state
	public void addTransition(NFAstate_VM<Symbol, Content> state, Symbol symbol, NFAstate_VM<Symbol, Content> targetState) {
		if (state == null)
			throw new NullPointerException();
		if (targetState == null)
			throw new NullPointerException();
		
		assert this.allStates.contains(state);
		assert this.allStates.contains(targetState);
		
		alphabet.add(symbol); // If the alphabet does not contain the symbol, add it
		assert this.alphabet.contains(symbol);
		state.addTransition(symbol, targetState);
	}
	
	// Is @word accepted by this automaton?
	boolean accepts(List<Symbol> word) {
		if (word == null)
			throw new NullPointerException();
		
		Set<NFAstate_VM<Symbol, Content>> presentStates = new TreeSet<NFAstate_VM<Symbol, Content>>();
		presentStates.addAll(initialStates);
		
		// Iterate over the word
		for (Symbol symbol : word) {
			Set<NFAstate_VM<Symbol, Content>> newStates = new TreeSet<NFAstate_VM<Symbol, Content>>();
			for (NFAstate_VM<Symbol, Content> state : presentStates)
				newStates.addAll(state.outTransitions.get(symbol));

			presentStates = newStates;
		}
		
		// Check if any state is accepting
		for (NFAstate_VM<Symbol, Content> state : presentStates)
			if (state.isAccepting)
				return true;
		
		return false;
	}
	
	// Exists a word that is accepted by this automaton?
	// If yes, return the run, else return null
	public NFArun<Symbol, Content> getAcceptingRun() {
		Set<NFAstate_VM<Symbol, Content>> marked = new HashSet<NFAstate_VM<Symbol, Content>>();
		List<INFAstate<Symbol, Content>> runStates = new ArrayList<INFAstate<Symbol, Content>>();
		List<Symbol> runWord = new ArrayList<Symbol>();
		boolean pathFound = false;
		for (NFAstate_VM<Symbol, Content> state : initialStates) {
			pathFound = findPath(state, marked, runStates, runWord);
			if (pathFound)
				break;
		}
		if (!pathFound)
			return null; // no accepting run exists
		
		// Reverse the run Lists, because the recursion created them backwards
		NFA_VM.reverseList(runStates);
		NFA_VM.reverseList(runWord);
		
		return new NFArun<Symbol, Content>(runWord, runStates);
	}
	private boolean findPath(NFAstate_VM<Symbol, Content> state, Set<NFAstate_VM<Symbol, Content>> marked, List<INFAstate<Symbol, Content>> runStates, List<Symbol> runWord) {
		if (marked.contains(state))
			return true;
		marked.add(state);
		
		// Check if state is accepting
		if (state.isAccepting) {
			runStates.add(state);
			return true;
		}
		
		// Check the transitions
		for (Map.Entry<Symbol, Collection<NFAstate_VM<Symbol, Content>>> transition : state.outTransitions.entrySet())
			for (NFAstate_VM<Symbol, Content> nextState : transition.getValue()) {
				boolean pathExists = findPath(nextState, marked, runStates, runWord);
				if (pathExists) {
					runStates.add(state);
					runWord.add(transition.getKey());
					return true;
				}
			}
		
		// None found
		return false;
	}
	private static <T> void reverseList(List<T> list) {
		int n = list.size();
		for (int i = 0; i < (n / 2); ++i) {
			T tmp = list.get(i);
			list.set(i, list.get(n - 1 - i));
			list.set(n - 1 - i, tmp);
		}
	}
	
	public NFA_VM<Symbol, Content> intersect(NFA_VM<Symbol, Content> automaton) {
		if (automaton == null)
			throw new NullPointerException();
		
		NFA_VM<Symbol, Content> result = new NFA_VM<Symbol, Content>(this.contentFactory);
		result.alphabet.addAll(this.alphabet);
		result.alphabet.addAll(automaton.alphabet);
		Map<NFAstate_VM<Symbol, Content>, Map<NFAstate_VM<Symbol, Content>, NFAstate_VM<Symbol, Content>>> stateMap
			= new HashMap<NFAstate_VM<Symbol, Content>, Map<NFAstate_VM<Symbol, Content>, NFAstate_VM<Symbol, Content>>>();
		
		// Create new states
		for (NFAstate_VM<Symbol, Content> state : this.allStates) {
			Map<NFAstate_VM<Symbol, Content>, NFAstate_VM<Symbol, Content>> map2
				= new HashMap<NFAstate_VM<Symbol, Content>, NFAstate_VM<Symbol, Content>>();
			for (NFAstate_VM<Symbol, Content> aState : automaton.allStates) {
				NFAstate_VM<Symbol, Content> newState = new NFAstate_VM<Symbol, Content>();
				newState.content = this.contentFactory.createContentOnIntersection(state.content, aState.content);
				map2.put(aState, newState);
				result.allStates.add(newState);
				if (state.isAccepting && aState.isAccepting)
					newState.isAccepting = true;
			}
			stateMap.put(state, map2);
		}
		
		// Copy transitions
		for (NFAstate_VM<Symbol, Content> state : this.allStates) {
			for (NFAstate_VM<Symbol, Content> aState : automaton.allStates) {
				NFAstate_VM<Symbol, Content> newState = stateMap.get(state).get(aState);
				if (this.initialStates.contains(state) && automaton.initialStates.contains(aState))
					result.initialStates.add(newState);
				
				Collection<Symbol> transitionSymbols = new TreeSet<Symbol>();
				for (Symbol symbol : state.outTransitions.keySet())
					if (aState.outTransitions.containsKey(symbol))
						transitionSymbols.add(symbol);
				
				for (Symbol symbol : transitionSymbols) {
					Collection<NFAstate_VM<Symbol, Content>> next1 = state.outTransitions.get(symbol);
					Collection<NFAstate_VM<Symbol, Content>> next2 = aState.outTransitions.get(symbol);
					if (next1 != null && next2 != null)
						for (NFAstate_VM<Symbol, Content> oState : next1)
							for (NFAstate_VM<Symbol, Content> oaState : next2)
								newState.addTransition(symbol, stateMap.get(oState).get(oaState));
				}
			}
		}
		
		return result;
	}
	
	public void totalize() {
		// Add new sink state
		NFAstate_VM<Symbol, Content> discardingState = this.addState(false, false, contentFactory.createSinkStateContent());
		for (Symbol symbol : alphabet)
			discardingState.addTransition(symbol, discardingState);
		
		// Add all sink transitions
		boolean addedTransition = false;
		for (NFAstate_VM<Symbol, Content> state : allStates)
			for (Symbol symbol : alphabet)
				if (!state.outTransitions.containsKey(symbol)) {
					state.addTransition(symbol, discardingState);
					addedTransition = true;
				}
		
		// Check if sink state was needed
		if (!addedTransition)
			this.allStates.remove(discardingState);
	}
	
	public void complement() {
		this.determinize();
		this.totalize();
		
		// Total, deterministic automatons are inverted by inverting the accepting property in every state
		for (NFAstate_VM<Symbol, Content> state : allStates)
			state.isAccepting = !state.isAccepting;
	}
	
	public NFA_VM<Symbol, Content> union(NFA_VM<Symbol, Content> automaton) {
		if (automaton == null)
			throw new NullPointerException();
		
		// assert alphabet equality
		if (!(this.alphabet.containsAll(automaton.alphabet) && automaton.alphabet.containsAll(this.alphabet)))
				throw new UnsupportedOperationException();
		
		// A union B = ((A complement) intersection (B complement)) complement
		this.complement();
		automaton.complement();
		
		NFA_VM<Symbol, Content> result = this.intersect(automaton);
		result.complement();
		
		// Change @this and @automaton back to their original function
		this.complement();
		automaton.complement();
		
		return result;
	}
	
	public NFA_VM<Symbol, Content> difference(NFA_VM<Symbol, Content> automaton) {
		if (automaton == null)
			throw new NullPointerException();
		
		// A setminus B = A intersection (B complement)
		automaton.complement();
		NFA_VM<Symbol, Content> result = this.intersect(automaton);
		
		// Change @automaton back to its original function
		automaton.complement();
		
		return result;
	}
	
	public void determinize() {
		if(initialStates.size() > 1){
			ArrayList<Content> cList = new ArrayList<Content>();
			NFAstate_VM<Symbol, Content> initialState = new NFAstate_VM<Symbol, Content>();
			for(NFAstate_VM<Symbol, Content> state : initialStates){
				cList.add(state.getContent());
				initialState.isAccepting |= state.isAccepting;
				for(Symbol symbol : state.outTransitions.keySet()){
					Collection<NFAstate_VM<Symbol, Content>> col = state.outTransitions.get(symbol);
					boolean addInitialState = false;
					for(NFAstate_VM<Symbol, Content> tran : col)
						if(initialStates.contains(tran))
							addInitialState = true;
						else
							initialState.addTransition(symbol, tran);
					if(addInitialState)
						initialState.addTransition(symbol, initialState);
				}
			}
			initialState.content = contentFactory.createContentOnDeterminization(cList);
			for(NFAstate_VM<Symbol, Content> state : allStates){
				if(initialStates.contains(state))
					continue;
				Map<Symbol, Set<NFAstate_VM<Symbol, Content>>> deleteMap = new TreeMap<Symbol, Set<NFAstate_VM<Symbol, Content>>>(NFAstate_VM.CompareByHash.instance);
				for(Symbol symbol : state.outTransitions.keySet())
					for(NFAstate_VM<Symbol, Content> nextState : state.outTransitions.get(symbol))
						if(initialStates.contains(nextState))
							if(deleteMap.containsKey(symbol))
								deleteMap.get(symbol).add(nextState);
							else{
								HashSet<NFAstate_VM<Symbol, Content>> set = new HashSet<NFAstate_VM<Symbol, Content>>();
								set.add(nextState);
								deleteMap.put(symbol, set);
							}	
				for(Symbol symbol : deleteMap.keySet()){
					state.outTransitions.get(symbol).removeAll(deleteMap.get(symbol));
					state.addTransition(symbol, initialState);
				}
			}
		
			allStates.removeAll(initialStates);
			allStates.add(initialState);
			initialStates.clear();
			initialStates.add(initialState);
		}
		
		Queue<NFAstate_VM<Symbol, Content>> queue = new ConcurrentLinkedQueue<NFAstate_VM<Symbol, Content>>();
		Set<NFAstate_VM<Symbol, Content>> unvisitedStates = new HashSet<NFAstate_VM<Symbol, Content>>();
		Map<Collection<NFAstate_VM<Symbol, Content>>, NFAstate_VM<Symbol, Content>> combinedStates;
		combinedStates = new HashMap<Collection<NFAstate_VM<Symbol, Content>>, NFAstate_VM<Symbol, Content>>();
		unvisitedStates.addAll(allStates);
		queue.addAll(initialStates);
		
		while(!queue.isEmpty()){
			NFAstate_VM<Symbol, Content> state = queue.poll();
			if(!unvisitedStates.contains(state))
				continue;
			unvisitedStates.remove(state);
			
			for(Symbol s : state.outTransitions.keySet()){
				Collection<NFAstate_VM<Symbol, Content>> nextStates = state.outTransitions.get(s);
				if(nextStates.size() > 1){
					Collection<NFAstate_VM<Symbol, Content>> combinedStatesKey = new HashSet<NFAstate_VM<Symbol, Content>>();
					boolean allreadyExists = false;
					for(Collection<NFAstate_VM<Symbol, Content>> col : combinedStates.keySet())
						if(nextStates.containsAll(col) && col.size() == nextStates.size()){
							allreadyExists = true;
							combinedStatesKey = col;
							break;
						}
					HashSet<NFAstate_VM<Symbol, Content>> delete = new HashSet<NFAstate_VM<Symbol, Content>>();
					for(NFAstate_VM<Symbol, Content> s1 : nextStates){
						if(combinedStates.containsValue(s1))
							for(Collection<NFAstate_VM<Symbol, Content>> col :
								combinedStates.keySet())
								if(s1.equals(combinedStates.get(col)))
									for(NFAstate_VM<Symbol, Content> s2 : nextStates){
										if(!s1.equals(s2) && col.contains(s2)){
											delete.add(s2);
										}
									}
					}
					for(NFAstate_VM<Symbol, Content> s1 : delete)
						nextStates.remove(s1);
					if(nextStates.size() == 1)
						continue;
					if(allreadyExists){
						nextStates.clear();
						nextStates.add(combinedStates.get(combinedStatesKey));
					}
					else{
						NFAstate_VM<Symbol, Content> newState = new NFAstate_VM<Symbol, Content>();
						ArrayList<Content> clist = new ArrayList<Content>();
						for(NFAstate_VM<Symbol, Content> reachedState : nextStates){
							clist.add(reachedState.getContent());
							for(Symbol symbol : reachedState.outTransitions.keySet())
								newState.addTransition(symbol, reachedState.outTransitions.get(symbol));
							newState.isAccepting |= reachedState.isAccepting;
						}
						newState.content = contentFactory.createContentOnDeterminization(clist);
						allStates.add(newState);
						HashSet<NFAstate_VM<Symbol, Content>> set = new HashSet<NFAstate_VM<Symbol, Content>>();
						set.addAll(nextStates);
						nextStates.clear();
						nextStates.add(newState);
						unvisitedStates.add(newState);
						queue.add(newState);
						combinedStates.put(set, newState);
					}
				}
			}
			
			if(queue.isEmpty() && !unvisitedStates.isEmpty())
				queue.addAll(unvisitedStates);
		}
	}
	
	public void minimize() { 
		//this.determinize();
		
		Set<NFAstate_VM<Symbol, Content>> unreachableStates = new HashSet<NFAstate_VM<Symbol, Content>>();
		unreachableStates.addAll(allStates);
		Set<NFAstate_VM<Symbol, Content>> currentStates = new HashSet<NFAstate_VM<Symbol, Content>>();
		currentStates.addAll(initialStates);
		
		boolean someThingChanged = true;
		
		while(!unreachableStates.isEmpty() && !currentStates.isEmpty() && someThingChanged ) {
			Set<NFAstate_VM<Symbol, Content>> nextStates = new HashSet<NFAstate_VM<Symbol, Content>>();
			someThingChanged = false;
			
			for(NFAstate_VM<Symbol, Content> state : currentStates) 
				if(unreachableStates.contains(state)){
					unreachableStates.remove(state);
					for(Symbol symbol : state.outTransitions.keySet()) 
						nextStates.addAll(state.outTransitions.get(symbol));
					someThingChanged = true;
				}
			
			currentStates = nextStates;
		}
		allStates.removeAll(unreachableStates);
		
		class Pair{
			public NFAstate_VM<Symbol, Content> first;
			public NFAstate_VM<Symbol, Content> second;
			public Pair(NFAstate_VM<Symbol, Content> first, NFAstate_VM<Symbol, Content> second){
				this.first = first;
				this.second = second;
			}
			
			/*public int hashCode(){
				return first.hashCode()+ second.hashCode();
			}*/
			
			public boolean equals(Object other){
				if(other.getClass().equals(Pair.class)){
					Pair o = (Pair)other;
					return (first.equals(o.first) && second.equals(o.second)) || (first.equals(o.second) && second.equals(first));
				}
				return false;
			}
		}
		
		HashMap<Pair, Boolean> pairs = new HashMap<Pair, Boolean>();
		HashSet<NFAstate_VM<Symbol, Content>> states = new HashSet<NFAstate_VM<Symbol, Content>>();
		states.addAll(allStates);
		for (NFAstate_VM<Symbol, Content> s1 : allStates){
			states.remove(s1);
			for (NFAstate_VM<Symbol, Content> s2 : states){
					Pair pair = new Pair(s1, s2);
					pairs.put(pair, s1.isAccepting || s2.isAccepting);
			}
		}
		
		someThingChanged = true;
		
		while(someThingChanged) {
			someThingChanged = false;
			HashSet<Pair> changedPairs = new HashSet<Pair>();
			for(Pair pair : pairs.keySet())
				if(!pairs.get(pair)){
					Set<Symbol> symbols = pair.first.outTransitions.keySet();
					symbols.retainAll(pair.second.outTransitions.keySet());
					for(Symbol symbol : symbols){
						NFAstate_VM<Symbol, Content> first = new NFAstate_VM<Symbol, Content>(),
						second = new NFAstate_VM<Symbol, Content>();
						for(NFAstate_VM<Symbol, Content> state : pair.first.outTransitions.get(symbol))
							first = state;
						for(NFAstate_VM<Symbol, Content> state : pair.second.outTransitions.get(symbol))
							second = state;
						if(!first.equals(second))
							for(Pair p : pairs.keySet())
								if( (p.first.equals(first) && p.second.equals(second)) || (p.first.equals(second) && p.second.equals(first)) )
									if(pairs.get(p)){
										changedPairs.add(pair);
										someThingChanged = true;
										break;
									}
					}
				}
			for(Pair pair : changedPairs){
				pairs.remove(pair);
				pairs.put(pair, true);
			}
		}
		
		ArrayList<HashSet<NFAstate_VM<Symbol, Content>>> mixedStates = new ArrayList<HashSet<NFAstate_VM<Symbol, Content>>>();
		for(Pair pair : pairs.keySet())
			if(!pairs.get(pair)){
				boolean newOne = true;
				for(int i=0;i<mixedStates.size();i++)
					if(mixedStates.get(i).contains(pair.first) || mixedStates.get(i).contains(pair.second)){
						mixedStates.get(i).add(pair.first);
						mixedStates.get(i).add(pair.second);
						newOne = false;
						break;
					}
				if(newOne){
					HashSet<NFAstate_VM<Symbol, Content>> set = new HashSet<NFAstate_VM<Symbol, Content>>();
					set.add(pair.first);
					set.add(pair.second);
					mixedStates.add(set);
				}
			}
		
		for(HashSet<NFAstate_VM<Symbol, Content>> set : mixedStates){
			NFAstate_VM<Symbol, Content> newState = new NFAstate_VM<Symbol, Content>();
			ArrayList<Content> list = new ArrayList<Content>();
			for(NFAstate_VM<Symbol, Content> s : set)
				list.add(s.getContent());
			newState.content = contentFactory.createContentOnMinimization(list);
			for(NFAstate_VM<Symbol, Content> state : set){
				newState.isAccepting |= state.isAccepting;
				for(Symbol symbol : state.outTransitions.keySet())
					newState.addTransition(symbol, state.outTransitions.get(symbol));
			}
			allStates.removeAll(set);
			allStates.add(newState);
			for(NFAstate_VM<Symbol, Content> state : allStates) 
				for(Symbol symbol : state.outTransitions.keySet())
					for(NFAstate_VM<Symbol, Content> nextState : state.outTransitions.get(symbol))
						if(set.contains(nextState)){
							nextState = newState;
						}
		}
	}
}
