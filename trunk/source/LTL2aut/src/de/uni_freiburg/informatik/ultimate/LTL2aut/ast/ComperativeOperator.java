package de.uni_freiburg.informatik.ultimate.LTL2aut.ast;



public class ComperativeOperator extends AstNode {
	
	ComperativeType type;
	
	public ComperativeOperator(ComperativeType type, AstNode left, AstNode right)
	{
		this.addOutgoing(left);
		this.addOutgoing(right);
		this.type = type;
	}
	
	public String toString()
	{
		String op = "??";
		switch(this.type){
			case equals: op = "="; break;
			case greater: op = ">"; break;
			case geq: op = ">="; break;
		}
		
		return this.getOutgoingNodes().get(0).toString() + op + this.getOutgoingNodes().get(1).toString();
	}

}
