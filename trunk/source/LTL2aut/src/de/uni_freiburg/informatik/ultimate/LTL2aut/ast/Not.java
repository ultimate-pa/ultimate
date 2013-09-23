package de.uni_freiburg.informatik.ultimate.LTL2aut.ast;

public class Not extends AstNode {
	
	public Not(AstNode child)
	{
		this.addOutgoing(child);
	}

	
	public String toString()
	{
		return "(!" + this.getOutgoingNodes().get(0).toString() + ")";
	}
}
