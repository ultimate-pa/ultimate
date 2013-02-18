/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.codan;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.result.IResult;

/**
 * Static class which stores the Ultimate Results per File. It is accessible for
 * all parts of the CDT-Plugin, especially for the Views.
 * 
 * @author Stefan Wissert
 * 
 */
public class CDTResultStore {

	/**
	 * The internal HashMap.
	 */
	private static HashMap<String, List<IResult>> fileToResults;

	/**
	 * Adds Results to the internal Map.
	 * 
	 * @param key
	 *            the filename
	 * @param value
	 *            list of results
	 */
	public static void addResults(String key, List<IResult> value) {
		if (fileToResults == null) {
			fileToResults = new HashMap<String, List<IResult>>();
		}
		fileToResults.put(key, value);
	}

	/**
	 * Returns the list with results.
	 * 
	 * @param key
	 *            the filename
	 * @return the list of results
	 */
	public static List<IResult> getResults(String key) {
		if (fileToResults != null && fileToResults.containsKey(key)) {
			return fileToResults.get(key);
		}
		return new ArrayList<IResult>();
	}
}
