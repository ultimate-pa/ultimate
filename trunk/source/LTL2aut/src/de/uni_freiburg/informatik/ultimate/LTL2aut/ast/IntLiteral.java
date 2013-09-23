package de.uni_freiburg.informatik.ultimate.LTL2aut.ast;

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

}
