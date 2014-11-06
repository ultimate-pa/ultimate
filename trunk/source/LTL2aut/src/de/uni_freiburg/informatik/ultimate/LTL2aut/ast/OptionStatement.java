package de.uni_freiburg.informatik.ultimate.ltl2aut.ast;

public class OptionStatement extends AstNode {
	
	private AstNode condition;
	
	public void setCondition(AstNode condition) {
		this.condition = condition;
	}

	public OptionStatement(AstNode condition, AstNode child)
	{
		this.condition = condition;
		this.addOutgoing(child);
	}
	
	public String toString()
	{
		return ":: (" + condition.toString() + ")-> " + this.getOutgoingNodes().get(0)+ "\n";
	}
	
	public AstNode getCondition()
	{
		return this.condition;
	}
	

}
