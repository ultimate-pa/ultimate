/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 * 
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.codan;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

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
			final ArrayList<IResult> compResults = new ArrayList<IResult>();
			for (final String toolId : fileToResults.get(key).keySet()) {
				final List<IResult> results = fileToResults.get(key).get(toolId);
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
