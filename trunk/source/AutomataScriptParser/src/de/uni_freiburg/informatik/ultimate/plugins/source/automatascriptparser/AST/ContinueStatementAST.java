package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;


public class ContinueStatementAST extends AtsASTNode {


	public ContinueStatementAST(ILocation loc) {
		super(loc);
	}

	private static final long serialVersionUID = 7627587071909794385L;

	@Override
	public String getAsString() {
		return "continue";
	}

	@Override
	public String toString() {
		return "ContinueStatement";
	}
	
	

}


