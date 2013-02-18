/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 */

public class ConditionalBooleanExpression extends AtsASTNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 8374243361020834074L;
	private ConditionalBooleanOperator m_operator;
	
	public ConditionalBooleanExpression() {
		m_returnType = Boolean.class;
		m_expectingType = m_returnType;
	}
	
	public ConditionalBooleanExpression(AtsASTNode element) {
		m_returnType = Boolean.class;
		m_expectingType = m_returnType;
		addOutgoingNode(element);
	}
	
	public ConditionalBooleanExpression(AtsASTNode element1, AtsASTNode element2) {
		m_returnType = Boolean.class;
		m_expectingType = m_returnType;
		addOutgoingNode(element1);
		addOutgoingNode(element2);
	}

	public ConditionalBooleanOperator getOperator() {
		return m_operator;
	}

	public void setOperator(ConditionalBooleanOperator operator) {
		this.m_operator = operator;
	}

	@Override
	public String toString() {
		return "ConditionalBooleanExpression [#Arguments: " + getOutgoingNodes().size() + ", Operator: " + m_operator + "]";
	}
}
