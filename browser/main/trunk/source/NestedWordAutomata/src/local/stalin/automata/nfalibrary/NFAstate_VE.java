package local.stalin.automata.nfalibrary;

import java.util.List;
import java.util.ArrayList;

public class NFAstate_VE<Symbol, Content extends StateContent> implements INFAstate<Symbol, Content> {
	
	public boolean isAccepting;
	public Content content;
	public List<NFAedge<Symbol, Content>> edges;

	public Content getContent() 
	{
		return content;
	}
	
	public NFAstate_VE()
	{
		edges = new ArrayList<NFAedge<Symbol, Content>>();
		isAccepting = false;
		content = null;
	}

	public boolean isAccepting()
	{
		return isAccepting;
	}
}
