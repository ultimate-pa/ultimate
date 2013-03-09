/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class VariableExpression extends AtsASTNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1274217864955285514L;
	private String m_Identifier;
	
	public VariableExpression(String identifier) {
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

}
