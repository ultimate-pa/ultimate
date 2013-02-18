package local.stalin.automata.nfalibrary;

import java.util.List;

public class NFArun<Symbol, Content extends StateContent> {
	private List<Symbol> sequenceOfSymbols;
	private List<INFAstate<Symbol, Content>> sequenceOfStates;
	
	public NFArun(List<Symbol> word, List<INFAstate<Symbol, Content>> states) {
		assert states.size() == word.size()+1;
		this.sequenceOfSymbols = word;
		this.sequenceOfStates = states;
	}

	public List<Symbol> getSequenceOfSymbols() {
		return sequenceOfSymbols;
	}

	public List<INFAstate<Symbol, Content>> getSequenceOfStates() {
		return sequenceOfStates;
	}

}
