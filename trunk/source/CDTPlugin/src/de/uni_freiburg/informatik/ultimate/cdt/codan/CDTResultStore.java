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

	private static List<IResult> hackyResultList;

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

	public static int addHackyResult(IResult result) {
		if (hackyResultList == null) {
			hackyResultList = new ArrayList<>();
		}
		hackyResultList.add(result);
		return hackyResultList.size() - 1;
	}

	public static IResult getHackyResult(int i) {
		if (hackyResultList == null) {
			hackyResultList = new ArrayList<>();
		}
		if (hackyResultList.size() - 1 < i) {
			return null;
		}
		return hackyResultList.get(i);
	}
	
	public static void clearHackyResults(){
		if (hackyResultList == null) {
			hackyResultList = new ArrayList<>();
		}
		hackyResultList.clear();
	}
	
	public static void clearResults(){
		if (fileToResults != null) {
			fileToResults.clear();
		}
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
				List<IResult> results = fileToResults.get(key).get(toolId);
				if(results == null){
					continue;
				}
				compResults.addAll(results);
			}
			return compResults;
		}
		return new ArrayList<IResult>();
	}
}
