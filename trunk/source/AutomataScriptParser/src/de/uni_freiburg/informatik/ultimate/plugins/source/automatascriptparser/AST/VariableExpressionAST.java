/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class VariableExpressionAST extends AtsASTNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1274217864955285514L;
	private String m_Identifier;
	
	public VariableExpressionAST(String identifier) {
		m_Identifier = identifier;
	}

	public String getIdentifier() {
		return m_Identifier;
	}

	public void setIdentifier(String identifier) {
		this.m_Identifier = identifier;
	}
	

	@Override
	public String toString() {
		return "VariableExpression [Identifier: " + m_Identifier + "]";
	}

	@Override
	public String getAsString() {
		return m_Identifier;
	}
	
	

}
