package de.uni_freiburg.informatik.ultimate.LTL2aut.ast;

import java.util.List;

public class LabeledBlock extends AstNode {

	private AstNode value;
	
	public LabeledBlock(AstNode o){
		this.value = o;
	}
	
	public LabeledBlock(AstNode value, AstNode child){
		this.value = value;
		this.addOutgoing(child);
	}
	
	public String toString(){
		String children = "";
		for(AstNode node: this.getOutgoingNodes())
			children += node.toString();
		return this.value.toString()+":\n"+ children + "\n";
	}
	
	public AstNode getValue()
	{
		return this.value;
	}
}
