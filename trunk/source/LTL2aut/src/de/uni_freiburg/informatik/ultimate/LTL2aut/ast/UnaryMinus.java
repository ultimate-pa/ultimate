package de.uni_freiburg.informatik.ultimate.LTL2aut.ast;

public class UnaryMinus extends AstNode {
	
	public UnaryMinus(AstNode child)
	{
		this.addOutgoing(child);
	}

	
	public String toString()
	{
		return "-" + this.getOutgoingNodes().get(0).toString();
	}

}
