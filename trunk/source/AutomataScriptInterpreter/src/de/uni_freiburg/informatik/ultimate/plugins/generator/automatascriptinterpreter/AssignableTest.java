/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.util.HashMap;
import java.util.Map;

/**
 * 
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AssignableTest {
	
	private static Map<Class<?>, Class<?>> m_primitiveToClassTypes;
	
	public static void initPrimitiveTypes() {
		m_primitiveToClassTypes = new HashMap<Class<?>, Class<?>>();
		m_primitiveToClassTypes.put(int.class, Integer.class);
		m_primitiveToClassTypes.put(boolean.class, Boolean.class);
	}
	
	public static boolean isAssignableFrom(Class<?> left, Class<?> right) {
		Class<?> leftSide = left;
		Class<?> rightSide = right;
		if (m_primitiveToClassTypes.containsKey(left)) {
			leftSide = m_primitiveToClassTypes.get(left);
		}
		if (m_primitiveToClassTypes.containsKey(right)) {
			rightSide = m_primitiveToClassTypes.get(right);
		}
		if (leftSide != null && rightSide != null) {
			return leftSide.isAssignableFrom(rightSide);
		} else {
			return false; 
		}
	}
}
