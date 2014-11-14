package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class ReturnStatementAST extends AtsASTNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = -5400530113807233706L;

	public ReturnStatementAST(ILocation loc, AtsASTNode expr) {
		super(loc);
		m_returnType = expr.getReturnType();
		m_expectingType = Object.class;
	}

	public ReturnStatementAST(ILocation loc) {
		super(loc);
		// TODO Auto-generated constructor stub
	}

	@Override
	public String toString() {
		return "ReturnStatement ";
	}

	@Override
	public String getAsString() {
		return "return";
	}
	
}

