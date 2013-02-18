package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class ReturnStatement extends AtsASTNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = -5400530113807233706L;

	public ReturnStatement(AtsASTNode expr) {
		m_returnType = expr.getReturnType();
		m_expectingType = Object.class;
	}

	public ReturnStatement() {
		// TODO Auto-generated constructor stub
	}

	@Override
	public String toString() {
		return "ReturnStatement ";
	}
}

