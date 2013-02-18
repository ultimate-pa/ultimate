package local.stalin.automata.nfalibrary;

import java.util.Collection;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Comparator;

import local.stalin.automata.nfalibrary.INFAstate;
import local.stalin.automata.nfalibrary.StateContent;

public class NFAstate_VM<Symbol, Content extends StateContent> implements INFAstate<Symbol, Content> {
	
	public boolean isAccepting;
	Content content;
	// Matthias: set to public, because not in same class as Stalin Model Transformer..
	public Map<Symbol, Collection<NFAstate_VM<Symbol, Content>>> outTransitions;
	
	// TreeMap comparer
	static class CompareByHash implements Comparator<Object> {
		@Override
		public int compare(Object o1, Object o2) {
			return o1.hashCode() - o2.hashCode();
		}
		static CompareByHash instance = new CompareByHash();
	}
	
	// Default constructor
	NFAstate_VM() {
		isAccepting = false;
		content = null;
		outTransitions = new TreeMap<Symbol, Collection<NFAstate_VM<Symbol, Content>>>(CompareByHash.instance);
	}
	
	// Copy constructor
	NFAstate_VM(NFAstate_VM<Symbol, Content> state) {
		// 
		isAccepting = state.isAccepting;
		content = state.content;
		// FIXME: content = new Content(state.content);
		outTransitions = new TreeMap<Symbol, Collection<NFAstate_VM<Symbol, Content>>>(CompareByHash.instance);
		// new outTransitions is not filled at this point
	}
	
	// State collection implementation
	private Collection<NFAstate_VM<Symbol, Content>> createCol() {
		// To be able to change the implementation of the StateSet at a single point
		return new TreeSet<NFAstate_VM<Symbol, Content>>(CompareByHash.instance);
	}
	
	@Override
	public Content getContent() {
		return content;
	}
	
	void addTransition(Symbol symbol, Collection<NFAstate_VM<Symbol, Content>> next) {
		Collection<NFAstate_VM<Symbol, Content>> transition = outTransitions.get(symbol);
		if (transition == null) {
			transition = createCol();
			outTransitions.put(symbol, transition);
		}
		transition.addAll(next);
	}
	
	void addTransition(Symbol symbol, NFAstate_VM<Symbol, Content> next) {
		Collection<NFAstate_VM<Symbol, Content>> transition = outTransitions.get(symbol);
		if (transition == null) {
			transition = createCol();
			outTransitions.put(symbol, transition);
		}
		transition.add(next);
	}
	
	public String toString(){
		return content.toString();
	}
}
