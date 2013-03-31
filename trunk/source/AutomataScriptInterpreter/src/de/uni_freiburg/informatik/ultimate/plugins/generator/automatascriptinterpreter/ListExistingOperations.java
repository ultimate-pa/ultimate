package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Create a list of all available operations.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class ListExistingOperations {
	
	private Map<String, Set<Class<?>>> m_ExistingOperations;
	private List<String> m_OperationList = new ArrayList<String>();

	public ListExistingOperations(
			Map<String, Set<Class<?>>> existingOperations) {
		m_ExistingOperations = existingOperations;
		for (String operation : m_ExistingOperations.keySet()) {
			for (Class<?> clazz : m_ExistingOperations.get(operation)) {
				for (Constructor<?> constructor : clazz.getConstructors()) {
					m_OperationList.add(constructorStringRepresentation(constructor));
				}
			}
		}
	}
	
	
	private String constructorStringRepresentation(Constructor<?> constructor) {
		StringBuilder result = new StringBuilder();
		result.append(constructor.getDeclaringClass().getSimpleName());
		result.append("(");
		for (int i=0; i<constructor.getParameterTypes().length; i++) {
			Class<?> clazz = constructor.getParameterTypes()[i];
			if (i!=0) {
				result.append(",");
			}
			result.append(clazz.getSimpleName());
		}
		result.append(")");
		return result.toString();
	}
	
	/**
	 * Representation of available operations. One line for each operation.
	 */
	public String prettyPrint() {
		StringBuilder result = new StringBuilder();
		String[] sorted = m_OperationList.toArray(new String[0]);
		Arrays.sort(sorted);
		for(String op : m_OperationList) {
			result.append(op);
			result.append(System.getProperty("line.separator"));
		}
		return result.toString();
	}

}
