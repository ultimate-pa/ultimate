package de.uni_freiburg.informatik.ultimate.LTL2aut.ast;



public class BinaryOperator extends AstNode {
	
	private BinaryType type;
	
	public BinaryOperator(BinaryType type)
	{
		this.type = type;
	}
	
	public BinaryOperator(BinaryType type, AstNode left, AstNode right)
	{
		this.type = type;
		this.addOutgoing(left);
		this.addOutgoing(right);
	}
	
	public String toString()
	{
		String op = " ?? ";
		if (this.type == BinaryType.and) op = " && ";
		if (this.type == BinaryType.or) op = " || ";
		if (this.type == BinaryType.minus) op = " - ";
		if (this.type == BinaryType.plus) op = " + ";
		if (this.type == BinaryType.times) op = " * ";
	 	
		String result = "( ";
		int i = 0;
		for(; i < this.getOutgoingNodes().size()-1; i++)
		{
			result += this.getOutgoingNodes().get(i).toString() + op;
		}
		result += this.getOutgoingNodes().get(i).toString();
		result += " )";
		return result;
	}
	
	public BinaryType getType()
	{
		return this.type;
	}

}
