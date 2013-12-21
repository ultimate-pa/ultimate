package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;


public class ContinueStatementAST extends AtsASTNode {


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


