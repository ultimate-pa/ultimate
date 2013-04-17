/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */

public class RelationalExpression extends AtsASTNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = -5806173754091876977L;
	private RelationalOperator m_operator;

	public RelationalOperator getOperator() {
		return m_operator;
	}

	public void setOperator(RelationalOperator operator) {
		this.m_operator = operator;
	}
	
	public RelationalExpression() {
		m_returnType = Boolean.class;
		m_expectingType = Integer.class;
	}

	@Override
	public String toString() {
		return "RelationalExpression [Operator: " + operatorToString(m_operator) + "]";
	}
	
	private String operatorToString(RelationalOperator ro) {
		switch(ro) {
		case LESSTHAN: return " < ";
		case LESS_EQ_THAN: return " <= ";
		case GREATERTHAN: return " > ";
		case GREATER_EQ_THAN: return " >= ";
		case EQ: return " == ";
		case NOT_EQ: return " != ";
		default: return "";
		}
	}

	public String getOperatorAsString() {
		return operatorToString(m_operator);
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
