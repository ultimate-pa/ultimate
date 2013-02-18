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
//		String dir = "";
//		ArrayList<Class<?>> cls = getClassesFromDirectory(dir);
//
//		// Iterate over all classes found in the given directory
//		for (Class<?> c : cls) {
//			
//			// Iterate over all methods from current class, in order to find
//			// the correct method, which should be invoked.
//			for (Method m : c.getMethods()) {
//				// If we have found a method which equals the method we want to invocated, we still
//				// have to check if the method has the correct parameter types.
//				if (m.getName().equals(methodName)) {
//					Class<?>[] paramTypes = m.getParameterTypes();
//					// If the current method does not have the correct number of parameters, this cannot be
//					// the method we want to call!
//					if ((arguments != null ? arguments.length : 0) == (paramTypes != null ? paramTypes.length : 0)) {
//						// If the method has the correct number of types, then check for each
//						// parameter whether it has the correct type.
//						boolean errorHappened = false;
//						for (int i = 0; i < paramTypes.length; i++) {
//							// If the parameter expected to be String, then just check if the argument
//							// implements the toString() method.
//							if (paramTypes[i].getName().equals(String.class.getName())) {
//								if (arguments[i] instanceof AtsASTNode) {
//									if (((AtsASTNode) arguments[i]).getReturnType().isPrimitive()) {
//										if (!(implementsToString(wrapperTypes.get(((AtsASTNode) arguments[i]).getReturnType().getName())))) {
//											m_errorMessage += "Method with correct name found, but argument i = " + (i + 1) + " has wrong type.\n"; 
//											m_errorMessage += ((AtsASTNode) arguments[i]).getReturnType().getName() + " does not implement the toString() method.\n ";
//											errorHappened = true;
//											break;
//										}
//									} else if (!(implementsToString(((AtsASTNode)arguments[i]).getReturnType()))) {
//										m_errorMessage += "Method with correct name found, but argument i = " + (i + 1) + " has wrong type.\n"; 
//										m_errorMessage += ((AtsASTNode) arguments[i]).getReturnType().getName() + " does not implement the toString() method. ";
//										errorHappened = true;
//										break;
//									}
//								}
//
//							} else if (paramTypes[i].isPrimitive()) {
//								if (arguments[i] instanceof AtsASTNode) {
//									if (!((wrapperTypes.get(paramTypes[i].getName())).isAssignableFrom(((AtsASTNode)arguments[i]).getReturnType()))) {
//										m_errorMessage += "Method with correct name found, but argument i = " + (i + 1) + " has wrong type.\n"; 
//										m_errorMessage += ((AtsASTNode) arguments[i]).getReturnType().getName() + " is not an instance of " + paramTypes[i];
//										errorHappened = true;
//										break;
//									}
//								}
//							} else if (arguments[i] instanceof AtsASTNode){
//								if (!(paramTypes[i].isAssignableFrom(((AtsASTNode)arguments[i]).getReturnType()))) {
//									m_errorMessage += "Method with correct name found, but argument i = " + (i + 1) + " has wrong type.\n"; 
//									m_errorMessage += ((AtsASTNode) arguments[i]).getReturnType().getName() + " is not an instance of " + paramTypes[i] + "\n";
//									errorHappened = true;
//									break;
//								}
//
//							}
//						}
//						if (!errorHappened) {
//							rightMethodFound = true;
//							foundMethod = m;
//							m_returnType = m.getReturnType();
//							m_errorMessage = "";
//							return true;
//						}
//					} else {
//						m_errorMessage += "Method found, but wrong number of parameters.\n";
//						m_errorMessage += "Expected number of arguments : " + paramTypes.length + " Got: " + arguments.length + "\n";
//						return false;
//					}
//				}
//			}
//		}
//		m_errorMessage += "No operation with name  " + methodName + " found!\n";
		return true;
	}
	
	
	@SuppressWarnings("unused")
	private ArrayList<Class<?>> getClassesFromDirectory(String dir) {
		File[] files = (new File(dir)).listFiles(new ClassFileFilter());
		ArrayList<Class<?>> cls = new ArrayList<Class<?>>();
		try {
			int idxOfClassPoint = 0;
			Class<?> c = null;
			for (File f : files) {
				idxOfClassPoint = f.getName().lastIndexOf('.');
				c = Class.forName("outputOperations." + f.getName().substring(0, idxOfClassPoint));
				cls.add(c);
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		return cls;
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
