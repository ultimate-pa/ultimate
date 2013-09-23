package de.uni_freiburg.informatik.ultimate.LTL2aut.ast;

public class Name extends AstNode {
	
	private String value = "default";
	
	public Name(String name)
	{
		this.value = name;
	}
	
	public String toString()
	{
		return value;
	}
	
	public String getIdent()
	{return this.value;}

}
