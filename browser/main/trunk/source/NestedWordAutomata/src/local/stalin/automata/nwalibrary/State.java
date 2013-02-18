package local.stalin.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;


public class State<S,C> implements IState<S, C> {
	private boolean isFinal;
	private C content;
	
	protected Map<S, Collection<IState<S, C>>> internalTransitions;
	protected Map<S, Collection<IState<S, C>>> callTransitions;
	protected Map<S, 
		Map<IState<S, C>, Collection<IState<S, C>>>> returnTransitions;
	
	// Default constructor
	public State(boolean isFinal, C content) {
		super();
		this.isFinal = isFinal;
		this.content = content;
		this.internalTransitions = new TreeMap<S, 
			Collection<IState<S, C>>>(CompareByHash.instance);
		this.callTransitions = new TreeMap<S, 
			Collection<IState<S, C>>>(CompareByHash.instance);
		this.returnTransitions = new TreeMap<S,	Map<IState<S, C>, 
			Collection<IState<S, C>>>>(CompareByHash.instance);
	}
	
	// Copy constructor
	public State(IState<S, C> state) {
		super();
		if (state == null)
			throw new NullPointerException();

		this.isFinal = state.isFinal();
		this.content = state.getContent(); // Content is copied by reference!

		// Transition relations are not added at this point, 
		// other routines take care of that
		this.internalTransitions = new TreeMap<S, 
		Collection<IState<S, C>>>(CompareByHash.instance);
		this.callTransitions = new TreeMap<S, 
		Collection<IState<S, C>>>(CompareByHash.instance);
		this.returnTransitions = new TreeMap<S,  	Map<IState<S, C>, 
			Collection<IState<S, C>>>>(CompareByHash.instance);
	}

	@Override
	public C getContent() {
		return this.content;
	}

	@Override
	public boolean isFinal() {
		return this.isFinal;
	}

	@Override
	public void setFinal(boolean isFinal) {
		this.isFinal = isFinal;
	}

	@Override
	public Collection<IState<S, C>> getInternalSucc(S symbol) {
		assert internalTransitions != null;
		if (internalTransitions.containsKey(symbol))
			return internalTransitions.get(symbol);
		else
			return new ArrayList<IState<S, C>>(0);
	}

	@Override
	public Collection<IState<S, C>> getCallSucc(S symbol) {
		assert callTransitions != null;

		if (callTransitions.containsKey(symbol))
			return callTransitions.get(symbol);
		else
			return new ArrayList<IState<S, C>>(0);
	}

	@Override
	public Collection<IState<S, C>> getReturnLinearPred(S symbol) {
		assert returnTransitions != null;

		if (returnTransitions.containsKey(symbol))
			return returnTransitions.get(symbol).keySet();
		else
			return new ArrayList<IState<S, C>>(0);
	}
	
	public Collection<IState<S, C>> getReturnLinearPredForSucc(S symbol,
			IState<S,C> succState) {
		assert returnTransitions != null;
		Map<IState<S,C>,Collection<IState<S, C>>> linPred2succ = returnTransitions.get(symbol);
		if (linPred2succ == null) {
			return new ArrayList<IState<S, C>>(0);
		}
		else {
			HashSet<IState<S, C>> result = new HashSet<IState<S,C>>();
			for (IState<S,C> linPred : linPred2succ.keySet()) {
				if (linPred2succ.get(linPred).contains(succState)) {
					result.add(linPred);
				}
			}
			return result;
		}
	}
	
	@Override
	public Collection<IState<S, C>> getReturnSucc(IState<S, C> stateLinPred, 
															S symbol) {
		assert returnTransitions != null;

		if (returnTransitions.containsKey(symbol) 
			&& returnTransitions.get(symbol).containsKey(stateLinPred))
			return returnTransitions.get(symbol).get(stateLinPred);
		else
			return new ArrayList<IState<S, C>>(0);
	}
	
	void addInternalTransition(S symbol, IState<S, C> succState) {
		assert internalTransitions != null;

		Collection<IState<S, C>> transition = internalTransitions.get(symbol);
		if (transition == null) {
			transition = new TreeSet<IState<S, C>>(CompareByHash.instance);
			internalTransitions.put(symbol, transition);
		}
			transition.add(succState);
	}
	
	void addInternalTransition(S symbol, Collection<IState<S, C>> succStates){
		assert internalTransitions != null;
		for (IState<S, C> succ : succStates) {
			addInternalTransition(symbol, succ);
		}
	}


	boolean delInternalTransition(S symbol, IState<S,C> succState) {
		if (internalTransitions.get(symbol) == null) {
			return false;
		}
		else {
			boolean existed = internalTransitions.get(symbol).remove(succState);
			if (internalTransitions.get(symbol).isEmpty()) {
				internalTransitions.remove(symbol);
			}
			return existed;
		}
	}


	void addCallTransition(S symbol, IState<S, C> succState) {
		assert callTransitions != null;

		Collection<IState<S, C>> transition = callTransitions.get(symbol);
		if (transition == null) {
			transition = new TreeSet<IState<S, C>>(CompareByHash.instance);
			callTransitions.put(symbol, transition);
		}
		transition.add(succState);
	}

	void addCallTransition(S symbol, Collection<IState<S, C>> succStates){
		assert internalTransitions != null;
		for (IState<S, C> succ : succStates) {
			addCallTransition(symbol, succ);
		}
	}


	boolean delCallTransition(S symbol, IState<S,C> succState) {
		if (callTransitions.get(symbol) == null) {
			return false;
		}
		else {
			boolean existed = callTransitions.get(symbol).remove(succState);
			if (callTransitions.get(symbol).isEmpty()) {
				callTransitions.remove(symbol);
			}
			return existed;
		}
	}


	void addReturnTransition(S symbol, IState<S, C> linearPred, 
			IState<S, C> succState) {
		assert returnTransitions != null;

		Map<IState<S, C>, Collection<IState<S, C>>> transition1 = 
			returnTransitions.get(symbol);
		if (transition1 == null) {
			transition1 = new TreeMap<IState<S, C>, 
				Collection<IState<S, C>>>(CompareByHash.instance);
			returnTransitions.put(symbol, transition1);
		}
		Collection<IState<S, C>> transition2 = transition1.get(linearPred);
		if (transition2 == null) {
			transition2 = new TreeSet<IState<S, C>>(CompareByHash.instance);
			transition1.put(linearPred, transition2);
		}
		transition2.add(succState);
	}


	void addReturnTransition(S symbol, IState<S, C> linearPred, 
									Collection<IState<S, C>> succStates){
		assert returnTransitions != null;
		for (IState<S, C> succ : succStates) {
			addReturnTransition(symbol, linearPred, succ);
		}
	}


	boolean delReturnTransition(S symbol, IState<S, C> linearPred, 
			IState<S, C> succState) {
		if (returnTransitions.get(symbol) == null) {
			return false;
		}
		else {
			boolean existed;
			Map<IState<S, C>, Collection<IState<S, C>>> linearPred2succState = 
				returnTransitions.get(symbol); 
			if (linearPred2succState.get(linearPred) == null) {
				return false;
			}
			else {
				existed= linearPred2succState.get(linearPred).remove(succState);
				if (linearPred2succState.get(linearPred).isEmpty()) {
					linearPred2succState.remove(linearPred);
				}
			}
			if (returnTransitions.get(symbol).isEmpty()) {
				returnTransitions.remove(symbol);
			}
			return existed;
		}
	}


	@Override
	public Collection<S> getSymbolsInternal() {
		assert internalTransitions != null;
		return this.internalTransitions.keySet();
	}

	@Override
	public Collection<S> getSymbolsCall() {
		assert callTransitions != null;
		return this.callTransitions.keySet();
	}

	@Override
	public Collection<S> getSymbolsReturn() {
		assert returnTransitions != null;
		return this.returnTransitions.keySet();
	}

	public String toString() {
		return (content == null) ? super.toString() : content.toString();
	}

	public int internalTransitions() {
		int quantity = 0;
		for (S symbol : internalTransitions.keySet()) {
			quantity += internalTransitions.get(symbol).size();
		}
		return quantity;
	}

	public int callTransitions() {
		int quantity = 0;
		for (S symbol : callTransitions.keySet()) {
			quantity += callTransitions.get(symbol).size();
		}
		return quantity;
	}

	public int returnTransitions() {
		int quantity = 0;
		for (S symbol : returnTransitions.keySet()) {
			for (IState<S,C> linPred : returnTransitions.get(symbol).keySet()) {
				quantity += returnTransitions.get(symbol).get(linPred).size();
			}
		}
	return quantity;
	}

}
