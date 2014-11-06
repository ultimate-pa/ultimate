package de.uni_freiburg.informatik.ultimate.ltl2aut.ast;

public class IntLiteral extends AstNode {
	
	int value;
	
	public IntLiteral(int value)
	{
		this.value = value;
	}
	
	public String toString()
	{
		return Integer.toString(this.value);
	}

	public int getValue()
	{
		return value;
	}
}
