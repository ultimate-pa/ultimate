/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 */
/*
 
 */
public class UnaryExpressionAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1809386058471685881L;
	private UnaryOperatorAST m_operator;
	
	public UnaryExpressionAST(ILocation loc) {
		super(loc);
		m_returnType = Integer.class;
		m_expectingType = m_returnType;
	}
	
	public UnaryExpressionAST(ILocation loc, VariableExpressionAST expr) {
		super(loc);
		m_returnType = Integer.class;
		m_expectingType = m_returnType;
		addOutgoingNode(expr);
	}
	
	public UnaryOperatorAST getOperator() {
		return m_operator;
	}

	public void setOperator(UnaryOperatorAST operator) {
		this.m_operator = operator;
	}

	@Override
	public String toString() {
		return "UnaryExpression [" + operatorToString(m_operator) + "]";
	}
	
	private String operatorToString(UnaryOperatorAST uo) {
		switch (uo) {
		case EXPR_PLUSPLUS: return " expr++ ";
		case EXPR_MINUSMINUS: return " expr-- ";
		case PLUSPLUS_EXPR: return " ++expr ";
		case MINUSMINUS_EXPR: return " --expr ";
		default: return "";
		}
	}

	public String getOperatorAsString() {
		return operatorToString(m_operator);
	}
	@Override
	public String getAsString() {
		switch (m_operator) {
		case EXPR_PLUSPLUS: return m_children.get(0).getAsString() + "++";
		case EXPR_MINUSMINUS: return m_children.get(0).getAsString() + "--";
		case PLUSPLUS_EXPR: return "++" + m_children.get(0).getAsString();
		case MINUSMINUS_EXPR: return "--" + m_children.get(0).getAsString();
		default: return "";
		}
	}
	
	
}
