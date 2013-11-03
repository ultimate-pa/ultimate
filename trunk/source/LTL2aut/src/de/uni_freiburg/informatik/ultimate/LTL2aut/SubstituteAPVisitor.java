package de.uni_freiburg.informatik.ultimate.LTL2aut;


import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.*;

/**
 * Substitute the identifiers inside an AST of a Promela Büchi automaton description
 * by the correct atomic propositions.
 * 
 * @author Langenfeld
 *
 */
public class SubstituteAPVisitor {
	
	private Map<String, AstNode> aps;
	private List<Name> toSubstitute = new ArrayList<Name>();
	private List<AstNode> toSubstituteParents = new ArrayList<AstNode>();
	
	/**
	 * 	Go visit and replace
	 * @param aps: map ident->Ast of the atomic propositions
	 * @param ast: ast of the Promela description of the Büchi automaton 
	 */
	public SubstituteAPVisitor(Map<String, AstNode> aps, AstNode ast)
	{
		this.aps = aps;
		this.visit(ast, null);
		
		//now substitute idents by asts at the occurences the visitor has found
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
	
	
	/*
	 * search for all occurences of an identiefier known to be an atomic proposition
	 */
	private void visit(AstNode node, AstNode parent)
	{
		if (node instanceof BoolLiteral)
			return;
		//int literal may not occure
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
			this.visit(((OptionStatement)node).getCondition(), node);
		}
		else
		{
			//blindly visit everything else
			for(AstNode a: node.getOutgoingNodes())
				this.visit(a, node);
		}
	}

}
