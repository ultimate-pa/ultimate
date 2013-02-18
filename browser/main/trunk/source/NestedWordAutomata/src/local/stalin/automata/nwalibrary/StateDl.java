package local.stalin.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * @author matthias
 *
 * @param <S>
 * @param <C>
 */
public class StateDl<S,C> extends State<S,C> implements	IStateDl<S,C> {
	protected Map<S, Collection<IStateDl<S,C>>> inCalls;
	protected Map<S, Collection<IStateDl<S,C>>> inInternals;
	// Information lost, i.e., inReturnsHierarc and inReturnsLinear not binded
	protected Map<S, Collection<IStateDl<S,C>>> inReturnsHierarc;
	protected Map<S, Collection<IStateDl<S,C>>> inReturnsLinear;
//	protected Map<S, Collection<IStateDl<S,C>>> callLinearSucc;
	protected Map<IStateDl<S,C>,Collection<S>> summaryCandidates;
	// a note by example:
	// {(q1,c,q2), (q2, i, q3), (q3,q1,r,q4)}
	// q2's inCalls contains (q1, c)
	// q3's inInternals contains (q2, i)
	// q4's inReturnsHierarc contains (q3, r)
	// q4's inReturnsLinear contains (q1, r) (q1, q4 of same context)
	// q1's summaryCandidates contains q4
	
	
	public StateDl(boolean isFinal, C content) {
		super(isFinal, content);
		// TODO: fill in following items
		inCalls = 
			new TreeMap<S, Collection<IStateDl<S,C>>>(CompareByHash.instance);
		inInternals = 
			new TreeMap<S, Collection<IStateDl<S,C>>>(CompareByHash.instance);
		inReturnsHierarc = 
			new TreeMap<S, Collection<IStateDl<S,C>>>(CompareByHash.instance);
		inReturnsLinear = 
			new TreeMap<S, Collection<IStateDl<S,C>>>(CompareByHash.instance);
//		callLinearSucc = 
//			new TreeMap<S, Collection<IStateDl<S,C>>>(CompareByHash.instance);
		summaryCandidates = 
			new TreeMap<IStateDl<S,C>, Collection<S>>(CompareByHash.instance); 
	}

	public StateDl(IState<S,C> state) {
		super(state);
		inCalls = 
			new TreeMap<S, Collection<IStateDl<S,C>>>(CompareByHash.instance);
		inInternals = 
			new TreeMap<S, Collection<IStateDl<S,C>>>(CompareByHash.instance);
		inReturnsHierarc = 
			new TreeMap<S, Collection<IStateDl<S,C>>>(CompareByHash.instance);
		inReturnsLinear = 
			new TreeMap<S, Collection<IStateDl<S,C>>>(CompareByHash.instance);
//		callLinearSucc = 
//			new TreeMap<S, Collection<IStateDl<S,C>>>(CompareByHash.instance);
		summaryCandidates = 
			new TreeMap<IStateDl<S,C>, Collection<S>>(CompareByHash.instance); 
	}

	
	public Collection<S> getInSymbolsCall() {
		assert (inCalls != null);
		return inCalls.keySet();	
	}

	
	public Collection<S> getInSymbolsInternal() {
		assert (inInternals != null);
		return inInternals.keySet();
	}

	
	public Collection<S> getInSymbolsReturn() {
		assert (inReturnsLinear != null);
		return inReturnsLinear.keySet(); // same as inReturnsHierarc.keySet()
	}

	
	public Collection<IStateDl<S,C>> getSummaryCandidates() {
		assert (summaryCandidates != null);
		return summaryCandidates.keySet();
	}
	

	
	
	public Collection<IStateDl<S,C>> getInCall(S symbol) {
		assert (inCalls != null);
		if (inCalls.containsKey(symbol))
			return inCalls.get(symbol);
		else
			return new ArrayList<IStateDl<S,C>>(0);
	}

	
	public Collection<IStateDl<S,C>> getInInternal(S symbol) {
		assert (inInternals != null);
		if (inInternals.containsKey(symbol))
			return inInternals.get(symbol);
		else
			// HashSet or ArrayList?			
			return new ArrayList<IStateDl<S,C>>(0);
	}

	
	public Collection<IStateDl<S,C>> getInReturnHierarc(S symbol) {
		assert (inReturnsHierarc != null);
		if (inReturnsHierarc.containsKey(symbol))
			return inReturnsHierarc.get(symbol);
		else
			return new ArrayList<IStateDl<S,C>>(0);	
	}

	
	public Collection<IStateDl<S,C>> getInReturnLinear(S symbol) {
	assert (inReturnsLinear != null);
	if (inReturnsLinear.containsKey(symbol))
		return inReturnsLinear.get(symbol);
	else
		return new ArrayList<IStateDl<S,C>>(0);	
	}
	
	
	@Override
	public Collection<S> getSummaryCandidateSymbol(
			IStateDl<S,C> summaryCandidate) {
		assert (summaryCandidates != null);
		if (summaryCandidates.containsKey(summaryCandidate)) {
			return summaryCandidates.get(summaryCandidate);
		}
		return new ArrayList<S>(0);	
	}

	
	
//	public Collection<IStateDl<S,C>> getcallLinearSucc(S symbol) {
//		assert (callLinearSucc != null);
//		if (callLinearSucc.containsKey(symbol))
//			return callLinearSucc.get(symbol);
//		else
//			return new ArrayList<IStateDl<S,C>>(0);	
//		}

	
	

	
	private void addInCallTransition(S symbol, IStateDl<S,C> predState) {
		assert inCalls != null;
		Collection<IStateDl<S,C>> predStates = inCalls.get(symbol);
		if (predStates == null) {
			predStates = new TreeSet<IStateDl<S,C>>(CompareByHash.instance);
			inCalls.put(symbol, predStates);
		}
		predStates.add(predState);
		
//		((StateDl<S,C>) predState).addCallTransition(symbol, this);
	}
	

	private boolean delInCallTransition(S symbol, IStateDl<S,C> predState) {
		assert inCalls != null;
		if (inCalls.get(symbol) == null) {
			return false;
		}
		else {
			boolean existed = inCalls.get(symbol).remove(predState);
			if (inCalls.get(symbol).isEmpty()) {
				inCalls.remove(symbol);
			}
			return existed; 
		}
	}
	
	
	private void addInInternalTransition(S symbol, IStateDl<S,C> predState) {
		assert inInternals != null;
		Collection<IStateDl<S,C>> predStates = inInternals.get(symbol);
		if (predStates == null) {
			predStates = new TreeSet<IStateDl<S,C>>(CompareByHash.instance);
			inInternals.put(symbol, predStates);
		}
		predStates.add(predState);
	}
	
	private boolean delInInternalTransition(S symbol, IStateDl<S,C> predState) {
		assert inInternals != null;
		if (inInternals.get(symbol) == null) {
			return false;
		}
		else {
			boolean existed = inInternals.get(symbol).remove(predState);
			if (inInternals.get(symbol).isEmpty()) {
				inInternals.remove(symbol);
			}
			return existed; 
		}
	}

	
	// Possibly not used in emptiness check
	private void addInReturnHierarcTransition(S symbol,IStateDl<S,C> hierarcPredState) {
		assert inReturnsHierarc != null;
		Collection<IStateDl<S,C>> hierarcPredStates = 
			inReturnsHierarc.get(symbol);
		if (hierarcPredStates == null) {
			hierarcPredStates = 
				new TreeSet<IStateDl<S,C>>(CompareByHash.instance);
			inReturnsHierarc.put(symbol, hierarcPredStates);
		}
		hierarcPredStates.add(hierarcPredState);
	}
	
	private boolean delInReturnHierarcTransition(S symbol,IStateDl<S,C> hierarcPredState) {
		assert inReturnsHierarc != null;
		if (inReturnsHierarc.get(symbol) == null) {
			return false;
		}
		else {
			boolean existed = inReturnsHierarc.get(symbol).remove(hierarcPredState);
			if (inReturnsHierarc.get(symbol).isEmpty()) {
				inReturnsHierarc.remove(symbol);
			}
			return existed; 
		}
	}


	void addInReturnLinearTransition(S symbol, IStateDl<S,C> linearPredState) {
		assert inReturnsLinear != null;
		Collection<IStateDl<S,C>> linearPredStates = 
			inReturnsLinear.get(symbol);
		if (linearPredStates == null) {
			linearPredStates = 
				new TreeSet<IStateDl<S,C>>(CompareByHash.instance);
			inReturnsLinear.put(symbol, linearPredStates);
		}
		linearPredStates.add(linearPredState);
	}
	
	private boolean delInReturnLinearTransition(S symbol,IStateDl<S,C> linearPredState) {
		assert inReturnsLinear != null;
		if (inReturnsLinear.get(symbol) == null) {
			return false;
		}
		else {
			boolean existed = inReturnsLinear.get(symbol).remove(linearPredState);
			if (inReturnsLinear.get(symbol).isEmpty()) {
				inReturnsLinear.remove(symbol);
			}
			return existed; 
		}
	}
	
	//toDo

	void addSummaryCandidate(IStateDl<S,C> summaryCandidate, S symbol) {
		assert summaryCandidate != null;
		Collection<S> returnSymbols = summaryCandidates.get(summaryCandidate); 
		if (returnSymbols == null) {
			returnSymbols = 
				new TreeSet<S>(CompareByHash.instance);
			summaryCandidates.put(summaryCandidate, returnSymbols);
		}
		returnSymbols.add(symbol);
	}
	
	private boolean delsummaryCandidateReturnSymbol(
									IStateDl<S,C> summaryCandidate, S symbol) {
		assert summaryCandidate != null;
		if (summaryCandidates.get(summaryCandidate) == null) {
			return false;
		}
		else {
			boolean existed = 
				summaryCandidates.get(summaryCandidate).remove(symbol);
			if (summaryCandidates.get(summaryCandidate).isEmpty()) {
				summaryCandidates.remove(summaryCandidate);
			}
			return existed; 
		}
	}	
	

//	void addLinearCallSucessor(S symbol, IStateDl<S,C> linSuccState) {
//		assert callLinearSucc != null;
//		Collection<IStateDl<S,C>> callLinSuccOfSymbol = callLinearSucc.get(symbol); 
//		if (callLinSuccOfSymbol == null) {
//			callLinSuccOfSymbol = 
//				new TreeSet<IStateDl<S,C>>(CompareByHash.instance);
//			callLinearSucc.put(symbol, callLinSuccOfSymbol);
//		}
//		callLinSuccOfSymbol.add(linSuccState);
//	}
//	
//	private boolean delLinearCallSucessor(S symbol, IStateDl<S,C> linSuccState) {
//		assert callLinearSucc != null;
//		if (callLinearSucc.get(symbol)==null) {
//			return false;
//		}
//		else {
//			return callLinearSucc.get(symbol).remove(callLinearSucc); 
//		}
//	}	
	
	
	
//	@Deprecated
//	void addSummaryCandidate(IStateDl<S,C> linearSuccState) {
//		assert summaryCandidates != null;
//		summaryCandidates.add(linearSuccState);
//	}

	
	@Override
	void addCallTransition(S symbol, IState<S,C> succState) {
		super.addCallTransition(symbol, succState);
		((StateDl<S,C>) succState).addInCallTransition(symbol, this);
	}
	
	@Override
	boolean delCallTransition(S symbol, IState<S,C> succState) {
		boolean existsOut = super.delCallTransition(symbol, succState);
		if (existsOut) {
			boolean existsIn;
			existsIn = ((StateDl<S, C>) succState).delInCallTransition(symbol, this);
			assert (existsIn) : "Inconsistently linked states" ;
			
		}
		return existsOut;
	}
	
	@Override
	void addInternalTransition(S symbol, IState<S,C> succState) {
		super.addInternalTransition(symbol, succState);
		((StateDl<S,C>) succState).addInInternalTransition(symbol, this);
	}
	
	
	boolean delInternalTransition(S symbol, IState<S,C> succState) {
		boolean existsOut = super.delInternalTransition(symbol, succState);
		if (existsOut) {
			boolean existsIn;
			existsIn = ((StateDl<S,C>) succState).delInInternalTransition(symbol, this);
			assert (existsIn) : "Inconsistently linked states" ;
		}
		return existsOut;
	}
	
	@Override
	void addReturnTransition(S symbol, IState<S,C> linearPredState, 
			IState<S,C> succState) {
		super.addReturnTransition(symbol, linearPredState, succState);
		((StateDl<S,C>) succState).addInReturnHierarcTransition(symbol, this);
		((StateDl<S,C>) succState).addInReturnLinearTransition(symbol, 
				(StateDl<S,C>) linearPredState);
		((StateDl<S,C>) linearPredState).addSummaryCandidate((IStateDl<S, C>) succState,
				symbol);
	}
	boolean delReturnTransition(S symbol, IState<S,C> linearPredState, 
			IState<S,C> succState) {
		StateDl<S,C> succStateDl = (StateDl<S, C>) succState;
		boolean existsOut = super.delReturnTransition(symbol, linearPredState, succState);
		if (existsOut) {
			// Remove this state from the successors InReturnHierarcTransitions
			// if this is not the hierarchical predecessor of succState for some
			// other linear predecessor of the successor under symbol.
			if (super.getReturnLinearPredForSucc(symbol, succState).isEmpty()) {
				boolean existsInHierarc = ((StateDl<S,C>) succState).
									delInReturnHierarcTransition(symbol, this);
				assert (existsInHierarc) : "Inconsistently linked states" ;
			}
			// Remove the linearPredState of the successors
			// InReturnLinearTransitions if linearPredState is not also the
			// linear predecessor state of succState for some other hierarchical
			// predecessor of the successor under symbol.
			if (succStateDl.getInReturnHierarcForLinearPred(
										symbol, linearPredState).isEmpty()) {
				boolean existsInLinear = ((StateDl<S,C>) succState).
					delInReturnLinearTransition(symbol, (IStateDl<S, C>)
															linearPredState);
				assert (existsInLinear) : "Inconsistently linked states" ;
			}
			// After making the InReturnLinearTransitions of the successor state
			// consistent check if linearPred is still a linear predecessor of
			// succState under symbol. If not, remove symbol (and succState if
			// necessary) from linPreds summaryCandidates.
			if (!succStateDl.getInReturnLinear(symbol).contains(linearPredState)) {
				boolean existsSummaryCandidateReturnSymbol = 
					((StateDl<S,C>) linearPredState).
					delsummaryCandidateReturnSymbol(succStateDl,symbol);
				assert (existsSummaryCandidateReturnSymbol) : 
					"Inconsistently linked states" ;
			}
		}
		return existsOut;
	}
	
	/**
	 * Get all states that have an outgoing return transition to this state for
	 * linear predecessor linPred labeled with symbol.
	 * @param symbol
	 * @param linPred
	 * @return
	 */
	Collection<IStateDl<S,C>> getInReturnHierarcForLinearPred(S symbol, IState<S,C> linPred) {
		Collection<IStateDl<S,C>> result = new HashSet<IStateDl<S,C>>();
		for (IStateDl<S,C> hierarcPred : getInReturnHierarc(symbol)) {
			if (hierarcPred.getReturnLinearPred(symbol) != null) {
				if (hierarcPred.getReturnLinearPred(symbol).contains(linPred)) {
					result.add(hierarcPred);
				}
			}
		}
		return result;
	}
	
	public boolean linkingIsConsistent() {
		for (S symbol : getSymbolsInternal()) {
			for (IState<S,C> succ : getInternalSucc(symbol)) {
				IStateDl<S,C> succDl = (IStateDl<S, C>) succ;
				if (!succDl.getInInternal(symbol).contains(this)) {
					assert(false);
					return false;
				}
			}
		}
		
		for (S symbol : getSymbolsCall()) {
			for (IState<S,C> succ : getCallSucc(symbol)) {
				IStateDl<S,C> succDl = (IStateDl<S, C>) succ;
				if (!succDl.getInCall(symbol).contains(this)) {
					assert(false);
					return false;
				}
			}
		}
		
		for (S symbol : getSymbolsReturn()) {
			for (IState<S,C> linearPred : getReturnLinearPred(symbol)) {
				for (IState<S,C> succ : getReturnSucc(linearPred,symbol)) {
					IStateDl<S,C> succDl = (IStateDl<S, C>) succ;
					if (!succDl.getInReturnHierarc(symbol).contains(this)) {
						assert(false);
						return false;
					}
					if (!succDl.getInReturnLinear(symbol).contains(linearPred)) {
						assert(false);
						return false;
					}
					StateDl<S,C> linearPredDl = (StateDl<S, C>) linearPred;
					if (!linearPredDl.getSummaryCandidateSymbol(succDl).contains(symbol)) {
						assert(false);
						return false;
					}
				}
			}
		}
		
		for (S symbol : getInSymbolsInternal()) {
			for (IState<S,C> pred : getInInternal(symbol)) {
				if (!pred.getInternalSucc(symbol).contains(this)) {
					assert(false);
					return false;
				}
			}
		}
		
		for (S symbol : getInSymbolsCall()) {
			for (IState<S,C> pred : getInCall(symbol)) {
				if (!pred.getCallSucc(symbol).contains(this)) {
					assert(false);
					return false;
				}
			}
		}
		
		for (S symbol : getInSymbolsReturn()) {
			
			for (IState<S,C> hierarcPred : getInReturnHierarc(symbol)) {
				if (hierarcPred.getReturnLinearPred(symbol).isEmpty()) {
					assert(false);
					return false;
				}
			}
			
			for (IState<S,C> linearPred : getInReturnLinear(symbol)) {
				boolean existsHirarcPredWithReturn = false;
				for (IState<S,C> hierarcPred : getInReturnHierarc(symbol)) {
					StateDl<S,C> hierarcPredDl = (StateDl<S, C>) hierarcPred;
					if (hierarcPredDl.getReturnLinearPredForSucc(symbol, this).contains(linearPred)) {
						existsHirarcPredWithReturn = true;
					}
				}
				if(!existsHirarcPredWithReturn) {
					assert(false);
					return false;
				}
			}
			
			for (IState<S,C> linearPred : getInReturnLinear(symbol)) {
				StateDl<S,C> linearPredDl = (StateDl<S, C>) linearPred; 
				if (!linearPredDl.getSummaryCandidateSymbol(this).contains(symbol)) {
					assert(false);
					return false;
				}
			}
		}
		
		
		for (IState<S,C> summaryCandidate : getSummaryCandidates()) {
			IStateDl<S,C> summaryCandidateDl = (IStateDl<S,C>) summaryCandidate;
			for (S symbol : getSummaryCandidateSymbol(summaryCandidateDl)) {
				if(!summaryCandidateDl.getInReturnLinear(symbol).contains(this)) {
					assert(false);
					return false;
				}
			}
		}

		return true;
	}


	
	
	
	
	public void removeState(StateDl<S,C> state, NestedWordAutomaton<S, C> nwa) {
		StateDl<S,C> stateDl = (StateDl<S,C>) state;

		List<S> symbolsInternal = new ArrayList<S>(state.getInSymbolsInternal());
		for(S symbol : symbolsInternal) {
			List<IState<S,C>> predecessors = 
				new ArrayList<IState<S,C>>(state.getInInternal(symbol));
			for (IState<S,C> pred : predecessors) {
				StateDl<S,C> predDl = (StateDl<S,C>) pred;
				boolean existed = predDl.delInternalTransition(symbol, state);
				assert(existed);
			}
		}
		List<S> symbolsCall = new ArrayList<S>(state.getInSymbolsCall());
		for(S symbol : symbolsCall) {
			List<IState<S,C>> predecessors = 
				new ArrayList<IState<S,C>>(state.getInCall(symbol));
			for (IState<S,C> pred : predecessors) {
				StateDl<S,C> predDl = (StateDl<S,C>) pred;
				boolean existed = predDl.delCallTransition(symbol, state);
				assert(existed);
			}
		}
		List<S> symbolsReturn = new ArrayList<S>(state.getInSymbolsReturn());
		for(S symbol : symbolsReturn) {
			List<IState<S,C>> linPreds = new ArrayList<IState<S,C>>(state.getInReturnLinear(symbol));
			for (IState<S,C> linPred : linPreds) {
				StateDl<S,C> linPredDl = (StateDl<S,C>) linPred;
				List<IState<S,C>> hieracPreds = new ArrayList<IState<S,C>>(stateDl.getInReturnHierarcForLinearPred(symbol,linPredDl));
				for (IState<S,C> hieracPred : hieracPreds) {
					StateDl<S, C> hieracPredDl = (StateDl<S,C>) hieracPred;
					boolean existed = hieracPredDl.delReturnTransition(symbol, linPred, state);
					//FIXME find out about following assertion
//					assert(existed);
				}
			}
		}


		symbolsInternal = new ArrayList<S>(state.getSymbolsInternal());
		for (S symbol: symbolsInternal) {
			List<IState<S,C>> internalSuccs = new ArrayList<IState<S,C>>(state.getInternalSucc(symbol));
			for (IState<S,C> succ : internalSuccs) {
				boolean existed =
					state.delInternalTransition(symbol, succ);
				assert(existed);
			}
		}
		symbolsCall = new ArrayList<S>(state.getSymbolsCall());
		for (S symbol: symbolsCall) {
			List<IState<S,C>> callSuccs = new ArrayList<IState<S,C>>(state.getCallSucc(symbol));
			for (IState<S,C> succ : callSuccs) {
				boolean existed =
					state.delCallTransition(symbol, succ);
				assert(existed);
			}
		}
		symbolsReturn = new ArrayList<S>(state.getSymbolsReturn());
		for (S symbol: symbolsReturn) {
			List<IState<S,C>> returnLinPreds = new ArrayList<IState<S,C>>(state.getReturnLinearPred(symbol));
			for (IState<S,C> caller : returnLinPreds) {
				List<IState<S,C>> returnSuccs = new ArrayList<IState<S,C>>(state.getReturnSucc(caller,symbol));
				for (IState<S,C> succ : returnSuccs) {
					boolean existed =
						state.delReturnTransition(symbol,caller,succ);
					assert(existed) : "This could also be a wrong assertion";
				}
			}
		}
		
		nwa.getInitialStates().remove(state);
		nwa.getFinalStates().remove(state);
		boolean existed = nwa.getAllStates().remove(state);
		assert (existed);
	}


}
