/**
 * Valuation for the counter example result class.
 */
package de.uni_freiburg.informatik.ultimate.result;

import java.util.AbstractMap.SimpleEntry;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.IType;

/**
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 02.01.2012
 */
public interface IValuation {

	/**
	 * This method returns the Variable Values for current position on the
	 * failure path. How this is done is in the responsibility of each
	 * ModelChecker, that have to implement this interface.
	 * <br><br>
	 * The method returns a map which maps from the variable name to the values.
	 * The values are modeled as SimpleEntry<IType, List<String>>, where IType
	 * signals the type of the Variable (so Integer, Double or Array<Integer>)
	 * and the List represent the values of the single variable or the array.
	 * 
	 * @param index
	 *            the current position on the failure path.
	 * @return the values as Strings for the variables.
	 */
	public Map<String, SimpleEntry<IType, List<String>>> getValuesForFailurePathIndex(
			int index);

}
