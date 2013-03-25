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
	private static HashMap<String, HashMap<String, List<IResult>>> fileToResults;

	/**
	 * Adds Results to the internal Map.
	 * 
	 * @param file
	 *            the filename
	 * @param tool
	 *            the reporting tool
	 * @param value
	 *            list of results
	 */
	public static void addResults(String file, String tool, List<IResult> value) {
		if (fileToResults == null) {
			fileToResults = new HashMap<String, HashMap<String, List<IResult>>>();
		}
		if (!fileToResults.containsKey(file)) {
			fileToResults.put(file, new HashMap<String, List<IResult>>());
		}
		fileToResults.get(file).put(tool, value);
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
			ArrayList<IResult> compResults = new ArrayList<IResult>();
			for (String toolId : fileToResults.get(key).keySet()) {
				compResults.addAll(fileToResults.get(key).get(toolId));
			}
			return compResults;
		}
		return new ArrayList<IResult>();
	}
}
