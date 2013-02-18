package local.stalin.automata.nfalibrary;

public class NFAedge<Symbol, Content extends StateContent>
{
	public NFAstate_VE<Symbol, Content> predecessor, successor;
	public Symbol symbol;
}
