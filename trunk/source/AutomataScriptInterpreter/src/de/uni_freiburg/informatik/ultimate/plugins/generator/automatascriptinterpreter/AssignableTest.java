/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.util.HashMap;
import java.util.Map;

/**
 * Handles assignable tests for type checks. It is mainly used in the type checker
 * for automatascript test files. 
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AssignableTest {
	/** 
	 * A map from primitive types to reference types.
	 * e.g. (int -> Integer)
	 */
	private static Map<Class<?>, Class<?>> m_primitiveToClassTypes;
	
	public static void initPrimitiveTypes() {
		m_primitiveToClassTypes = new HashMap<Class<?>, Class<?>>();
		/* 
		 * In automata script test files, currently only two primitive types
		 * are in use, namely int and boolean.
		 */
		m_primitiveToClassTypes.put(int.class, Integer.class);
		m_primitiveToClassTypes.put(boolean.class, Boolean.class);
	}
	
	
	/**
	 * Performs an assignable test on two types. Can also handle
	 * primitive types. 
	 * @param left the type of the operand on the left-side of the assignment
	 * @param right the type of the operand on the right-side of the assignment
	 * @return true if and only if the right operand is equal to or a sub-type of the left operand,
	 * otherwise false.
	 */
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
