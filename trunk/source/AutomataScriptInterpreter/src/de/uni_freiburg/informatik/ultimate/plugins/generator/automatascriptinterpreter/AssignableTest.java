/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptInterpreter plug-in.
 * 
 * The ULTIMATE AutomataScriptInterpreter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptInterpreter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptInterpreter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptInterpreter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptInterpreter plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.util.HashMap;
import java.util.Map;

/**
 * Handles assignable tests for type checks. It is mainly used in the type checker for automatascript test files.
 * 
 * @author musab@informatik.uni-freiburg.de
 */
public class AssignableTest {
	/**
	 * A map from primitive types to reference types.
	 * e.g. (int -> Integer)
	 */
	private static Map<Class<?>, Class<?>> sPrimitiveToClassTypes;
	
	/**
	 * Initializes primitive types.
	 */
	public static void initPrimitiveTypes() {
		sPrimitiveToClassTypes = new HashMap<>();
		/*
		 * In automata script test files, currently only two primitive types
		 * are in use, namely int and boolean.
		 */
		sPrimitiveToClassTypes.put(int.class, Integer.class);
		sPrimitiveToClassTypes.put(boolean.class, Boolean.class);
	}
	
	/**
	 * Performs an assignable test on two types. Can also handle
	 * primitive types.
	 * 
	 * @param left
	 *            the type of the operand on the left-side of the assignment
	 * @param right
	 *            the type of the operand on the right-side of the assignment
	 * @return true if and only if the right operand is equal to or a sub-type
	 *         of the left operand, otherwise false.
	 */
	public static boolean isAssignableFrom(final Class<?> left, final Class<?> right) {
		Class<?> leftWithoutPrimitive = left;
		Class<?> rightWithoutPrimitive = right;
		boolean result;
		if (sPrimitiveToClassTypes.containsKey(left)) {
			leftWithoutPrimitive = sPrimitiveToClassTypes.get(left);
		}
		if (sPrimitiveToClassTypes.containsKey(right)) {
			rightWithoutPrimitive = sPrimitiveToClassTypes.get(right);
		}
		if (leftWithoutPrimitive != null && rightWithoutPrimitive != null) {
			result = leftWithoutPrimitive.isAssignableFrom(rightWithoutPrimitive);
		} else {
			result = false;
		}
		return result;
	}
}
