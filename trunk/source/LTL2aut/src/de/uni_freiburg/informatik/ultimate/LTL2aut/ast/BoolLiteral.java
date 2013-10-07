package de.uni_freiburg.informatik.ultimate.LTL2aut.ast;

public class BoolLiteral extends AstNode {
	
	boolean value;
	
	public BoolLiteral(boolean value)
	{
		this.value = value;
	}
	
	public String toString()
	{
		return Boolean.toString(this.value);
	}
	
	public boolean getValue()
	{
		return this.value;
	}

}
