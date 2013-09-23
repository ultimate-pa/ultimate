package de.uni_freiburg.informatik.ultimate.LTL2aut;


import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.*;

public class SubstituteAPVisitor {
	
	private Map<String, AstNode> aps;
	private List<Name> toSubstitute = new ArrayList<Name>();
	private List<AstNode> toSubstituteParents = new ArrayList<AstNode>();
	
	public SubstituteAPVisitor(Map<String, AstNode> aps, AstNode ast)
	{
		this.aps = aps;
		this.visit(ast, null); // a single name will not get parsed
		
		for(int i = 0; i < this.toSubstitute.size(); i++)
		{
			if (this.toSubstituteParents.get(i) instanceof OptionStatement)
			{
				((OptionStatement)this.toSubstituteParents.get(i)).setCondition(this.aps.get(this.toSubstitute.get(i).getIdent()));
			}
			else
			{
				this.toSubstituteParents.get(i).removeOutgoing(this.toSubstitute.get(i));
				this.toSubstituteParents.get(i).addOutgoing(this.aps.get(this.toSubstitute.get(i).getIdent()));
			}
		}
	}
	
	public void visit(AstNode node, AstNode parent)
	{
		if (node instanceof BoolLiteral)
			return;
		else if (node instanceof IntLiteral)
			return;
		else if (node instanceof Name)
		{
			Name n = (Name)node;
			if(this.aps.containsKey(n.getIdent()))
			{
				this.toSubstitute.add(n);
				this.toSubstituteParents.add(parent);
			}
		}
		else if (node instanceof OptionStatement)
		{
			//this.visit(node.getOutgoingNodes().get(0), node);    //not necessary!
			this.visit(((OptionStatement)node).getCondition(), node);
		}
		else
		{
			for(AstNode a: node.getOutgoingNodes())
				this.visit(a, node);
		}
	}

}
