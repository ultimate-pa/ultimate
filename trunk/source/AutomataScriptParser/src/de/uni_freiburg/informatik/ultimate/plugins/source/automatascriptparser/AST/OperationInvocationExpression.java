/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;


/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class OperationInvocationExpression extends AtsASTNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -2607691105145027619L;
	private String m_operationName;
	private String m_errorMessage;
	private String m_argsAsString;
	
	public OperationInvocationExpression(String opName, AtsASTNode e2) {
		m_operationName = opName;
		m_errorMessage = "";
		addOutgoingNode(e2);
	}
	
	public String getErrorMessage() {
		return m_errorMessage;
	}

	public String getOperationName() {
		return m_operationName;
	}

		
	public void setErrorMessage(String errorMessage) {
		this.m_errorMessage = errorMessage;
	}
	
	public void setOperationName(String opName) {
		this.m_operationName = opName;
	}
	
	
	@Override
	public String toString() {
		return "OperationExpression [Operation: " + m_operationName + "]";
	}

	public String getArgsAsString() {
		return m_argsAsString;
	}

	public void setArgsAsString(String m_argsAsString) {
		this.m_argsAsString = m_argsAsString;
	}

	@Override
	public String getAsString() {
		return m_operationName + "(" + m_children.get(0).getAsString() + ")";
	}
	

}
