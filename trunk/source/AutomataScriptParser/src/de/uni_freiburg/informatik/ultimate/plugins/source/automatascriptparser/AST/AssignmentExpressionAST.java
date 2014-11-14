package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
/**
 * @author musab@informatik.uni-freiburg.de
 *
 */

public class AssignmentExpressionAST extends AtsASTNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = -7311672964327139443L;
	private AssignmentOperatorAST m_operator;
	
	public AssignmentOperatorAST getOperator() {
		return m_operator;
	}

	public void setOperator(AssignmentOperatorAST operator) {
		this.m_operator = operator;
	}
	
	public AssignmentExpressionAST(ILocation loc, VariableExpressionAST var, AssignmentOperatorAST operator, AtsASTNode value) {
		super(loc);
		setOperator(operator);
		addOutgoingNode(var);
		addOutgoingNode(value);
		m_returnType = var.getReturnType();
		m_expectingType = m_returnType;
	}

	@Override
	public String toString() {
		return "AssignmentExpression [AssignmentOperator: " + operatorToString(m_operator) + "]";
	}
	
	private String operatorToString(AssignmentOperatorAST o) {
		switch (o) {
		case ASSIGN: return " := ";
		case PLUSASSIGN: return " += ";
		case MINUSASSIGN: return " -= ";
		case MODASSIGN: return " %= ";
		case MULTASSIGN: return " *= ";
		case DIVASSIGN: return " /= ";
		default: return "";
		}
	}

	@Override
	public String getAsString() {
		AtsASTNode var = null;
		AtsASTNode value = null;
		for (AtsASTNode n : m_children) {
			if (n instanceof VariableExpressionAST) {
				var = n;
			} else {
				value = n;
			}
		}
		return var.getAsString() + operatorToString(m_operator) + value.getAsString(); 
	}

}
