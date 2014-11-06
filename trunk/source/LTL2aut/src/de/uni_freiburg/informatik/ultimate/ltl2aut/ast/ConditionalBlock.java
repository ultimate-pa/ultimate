package de.uni_freiburg.informatik.ultimate.ltl2aut.ast;

import java.util.ArrayList;

public class ConditionalBlock extends AstNode {
	
	public ConditionalBlock(ArrayList<AstNode> o)
	{
		this.addAllOutgoing(o);
	}
	
	public String toString()
	{
		String result = "if\n";
		for(AstNode node: this.getOutgoingNodes())
			result += node.toString();
		result += "fi;\n";
		return result;
	}

}
