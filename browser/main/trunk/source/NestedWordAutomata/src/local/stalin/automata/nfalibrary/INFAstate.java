package local.stalin.automata.nfalibrary;

import local.stalin.automata.nfalibrary.StateContent;

public interface INFAstate<Symbol,Content extends StateContent> {
	
	public Content getContent();
	
	
	
}
