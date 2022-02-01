/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Create a list of all available operations.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class ListExistingOperations {
	private final Map<String, Set<Class<?>>> mExistingOperations;
	private final List<String> mOperationList = new ArrayList<>();
	
	/**
	 * @param existingOperations
	 *            Existing operations (maps from string to class).
	 */
	public ListExistingOperations(final Map<String, Set<Class<?>>> existingOperations) {
		mExistingOperations = existingOperations;
		for (final Set<Class<?>> classes : mExistingOperations.values()) {
			for (final Class<?> clazz : classes) {
				for (final Constructor<?> constructor : clazz.getConstructors()) {
					mOperationList.add(constructorStringRepresentation(constructor));
				}
			}
		}
	}
	
	private static String constructorStringRepresentation(final Constructor<?> constructor) {
		final StringBuilder result = new StringBuilder();
		result.append(firstLetterToLowerCase(constructor.getDeclaringClass().getSimpleName()));
		result.append("(");
		boolean alreadySomeParameterAdded = false;
		for (int i = 0; i < constructor.getParameterTypes().length; i++) {
			final Class<?> clazz = constructor.getParameterTypes()[i];
			if (AutomataLibraryServices.class.isAssignableFrom(clazz)) {
				// do not add this parameter
				continue;
			}
			if (IStateFactory.class.isAssignableFrom(clazz)) {
				// do not add this parameter
				continue;
			}
			if (alreadySomeParameterAdded) {
				result.append(",");
			}
			result.append(clazz.getSimpleName());
			alreadySomeParameterAdded = true;
		}
		result.append(")");
		return result.toString();
	}
	
	/**
	 * @return Representation of available operations. One line for each operation.
	 */
	public String prettyPrint() {
		final StringBuilder result = new StringBuilder();
		final String[] sorted = mOperationList.toArray(new String[mOperationList.size()]);
		Arrays.sort(sorted);
		for (final String op : sorted) {
			result.append(op);
			result.append(System.getProperty("line.separator"));
		}
		return result.toString();
	}
	
	static String firstLetterToLowerCase(final String str) {
		return str.substring(0, 1).toLowerCase() + str.substring(1);
	}
}
