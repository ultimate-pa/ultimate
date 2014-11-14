/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 */

public class ConditionalBooleanExpressionAST extends AtsASTNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 8374243361020834074L;
	private ConditionalBooleanOperatorAST m_operator;
	
	public ConditionalBooleanExpressionAST(ILocation loc) {
		super(loc);
		m_returnType = Boolean.class;
		m_expectingType = m_returnType;
	}
	
	public ConditionalBooleanExpressionAST(ILocation loc, AtsASTNode element) {
		super(loc);
		m_returnType = Boolean.class;
		m_expectingType = m_returnType;
		addOutgoingNode(element);
	}
	
	public ConditionalBooleanExpressionAST(ILocation loc, AtsASTNode element1, AtsASTNode element2) {
		super(loc);
		m_returnType = Boolean.class;
		m_expectingType = m_returnType;
		addOutgoingNode(element1);
		addOutgoingNode(element2);
	}

	public ConditionalBooleanOperatorAST getOperator() {
		return m_operator;
	}

	public void setOperator(ConditionalBooleanOperatorAST operator) {
		this.m_operator = operator;
	}

	@Override
	public String toString() {
		return "ConditionalBooleanExpression [#Arguments: " + getOutgoingNodes().size() + ", Operator: " + m_operator + "]";
	}

	@Override
	public String getAsString() {
		if (m_children.size() == 2) {
			String operatorAsString = (m_operator == ConditionalBooleanOperatorAST.AND? "&&" : "||");
			return m_children.get(0).getAsString() + " " +
		           operatorAsString + " " +
				   m_children.get(1).getAsString();	
		           
		} else if (m_children.size() == 1) {
			return "!" + m_children.get(0).getAsString();
		} else {
			return "";
		}
		
	}
	
}
