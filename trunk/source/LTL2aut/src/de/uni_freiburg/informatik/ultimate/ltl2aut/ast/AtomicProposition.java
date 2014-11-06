package de.uni_freiburg.informatik.ultimate.ltl2aut.ast;

public class AtomicProposition extends AstNode {
	
	String ident;
	
	public AtomicProposition(String ident, AstNode child)
	{
		this.ident = ident;
		this.addOutgoing(child);
	}
	
	public String toString()
	{
		return ident + " : " + this.getOutgoingNodes().get(0).toString(); 
	}
	
	public String getIdent()
	{ return this.ident; }

}
