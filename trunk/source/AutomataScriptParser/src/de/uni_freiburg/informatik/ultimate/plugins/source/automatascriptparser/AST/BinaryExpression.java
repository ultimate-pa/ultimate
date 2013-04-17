/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de 
 */


public class BinaryExpression extends AtsASTNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 561094736879070816L;
	private BinaryOperator m_operator;
	
	public BinaryExpression() {
		m_returnType = Integer.class;
		m_expectingType = m_returnType;
	}
	
	public BinaryExpression(AtsASTNode leftChild, AtsASTNode rightChild) {
		m_returnType = Integer.class;
		m_expectingType = m_returnType;
		addOutgoingNode(leftChild);
		addOutgoingNode(rightChild);
	}

	
	public void setOperator(BinaryOperator op) {
		m_operator = op;
	}
	
	public BinaryOperator getOperator()
	{
		return m_operator;
	}

	public String getOperatorAsString() {
		return operatorToString(m_operator);
	}
	@Override
	public String toString() {
		return "BinaryExpression [Operator: " + operatorToString(m_operator) + "]";
	}
	
	private String operatorToString(BinaryOperator bo) {
		switch(bo) {
		case PLUS: return " + ";
		case MINUS: return " - ";
		case MULTIPLICATION: return " * ";
		case DIVISION: return " / ";
		default: return "";
		}
	}

	@Override
	public String getAsString() {
		if (m_children.size() == 2) {
			return m_children.get(0).getAsString() + 
		           operatorToString(m_operator) + 
				   m_children.get(1).getAsString();
		} else {
			return "";
		}
		
	}
	
	

}
