/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.io.File;
import java.io.FileFilter;
import java.util.ArrayList;
import java.util.HashMap;


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

	class ClassFileFilter implements FileFilter {
		  public boolean accept(File pathname) {
		    return pathname.getName().endsWith(".class");
		  }
		}
	
	private String m_operationName;
	private String m_errorMessage;
	private HashMap<String, Class<?>> m_wrapperTypes;
	
	public OperationInvocationExpression(String opName, AtsASTNode e2) {

		m_operationName = opName;
		m_errorMessage = "";
		m_wrapperTypes = new HashMap<String, Class<?>>();
		m_wrapperTypes.put("int", Integer.class);
		m_wrapperTypes.put("long", Long.class);
		m_wrapperTypes.put("double", Double.class);
		m_wrapperTypes.put("float", Float.class);
		m_wrapperTypes.put("boolean", Boolean.class);
		m_wrapperTypes.put("char", Character.class);
		m_wrapperTypes.put("byte", Byte.class);
		m_wrapperTypes.put("short", Short.class);
		addOutgoingNode(e2);
	}

	public boolean existsMethod(String methodName, Object[] arguments) {
		return true;
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

}
