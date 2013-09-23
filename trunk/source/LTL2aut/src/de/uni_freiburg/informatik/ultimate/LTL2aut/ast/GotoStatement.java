package de.uni_freiburg.informatik.ultimate.LTL2aut.ast;

public class GotoStatement extends AstNode {
	
	public GotoStatement(AstNode target)
	{
		this.addOutgoing(target);
	}
	
	public String toString()
	{
		return "goto "+ this.getOutgoingNodes().get(0).toString();
	}

}
