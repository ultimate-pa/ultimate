package de.uni_freiburg.informatik.ultimate.LTL2aut.ast;

import java.util.List;

public class NeverStatement extends AstNode {

	public NeverStatement() {
		super();
	}
	
	public NeverStatement(AstNode child){
		this.addOutgoing(child);
	}

	public String toString(){
		String children = "";
		for(AstNode node: this.getOutgoingNodes())
			children += node.toString();
		return "never {\n"+ children  +"}";
	}
	

}
