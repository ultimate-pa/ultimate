/*
 * Copyright (C) 2019 Julian Löffler (loefflju@informatik.uni-freiburg.de), Breee@github
 * Copyright (C) 2012-2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Struct to store a featurevector which contains several properties of a SMT Term.
 *
 * @author Julian Löffler
 *
 */
public class SMTFeature {
	public int numberOfFunctions = 0;
	public int numberOfQuantifiers = 0;
	public int numberOfVariables = 0;
	public int numberOfArrays = 0;
	public int numberOfSelectFunctions = 0;
	public int numberOfStoreFunctions = 0;
	public int dagsize = 0;
	public long treesize = 0;
	public int dependencyScore = 0;
	public ArrayList<Integer> variableEquivalenceClassSizes;
	public int biggestEquivalenceClass;
	public Map<String, Integer> occuringSorts = new HashMap<>();
	public Map<String, Integer> occuringFunctions = new HashMap<>();
	public Map<Integer, Integer> occuringQuantifiers = new HashMap<>();
	public boolean containsArrays = false;
	public ArrayList<String> assertionStack = new ArrayList<>();
	public int assertionStackHashCode = 0;
	public String solverresult = "";
	public String solvername = "";
	public double solvertime = 0.0;

	@Override
	public String toString() {
		try {
			final StringBuilder sb = new StringBuilder();
			sb.append("\n" + getCsvHeader(";") + "\n");
			sb.append(toCsv(";"));
			return sb.toString();
		} catch (final IllegalAccessException e) {
			e.printStackTrace();
		}
		return "";
	}

	private String mapToJson(final Map<?, ?> map) {
		return "{"
				+ map.entrySet().stream().map(e -> "\"" + e.getKey() + "\"" + ":" + String.valueOf(e.getValue()) + "")
						.collect(Collectors.joining(", "))
				+ "}";

	}

	public String toCsv(final String delimiter) throws IllegalAccessException {
		final StringBuilder sb = new StringBuilder();
		final ArrayList<String> values = new ArrayList<>();
		values.add(String.valueOf(numberOfFunctions));
		values.add(String.valueOf(numberOfQuantifiers));
		values.add(String.valueOf(numberOfVariables));
		values.add(String.valueOf(numberOfArrays));
		values.add(String.valueOf(dagsize));
		values.add(String.valueOf(treesize));
		values.add(String.valueOf(dependencyScore));
		values.add(String.valueOf(variableEquivalenceClassSizes));
		values.add(String.valueOf(biggestEquivalenceClass));
		values.add(mapToJson(occuringSorts));
		values.add(mapToJson(occuringFunctions));
		values.add(mapToJson(occuringQuantifiers));
		values.add(String.valueOf(containsArrays));
		values.add(String.valueOf(assertionStack));
		values.add(String.valueOf(assertionStackHashCode));
		values.add(String.valueOf(solverresult));
		values.add(String.valueOf(solvername));
		values.add(String.valueOf(solvertime));
		sb.append(String.join(delimiter, values));
		return sb.toString();
	}

	public static String getCsvHeader(final String delimiter) throws IllegalAccessException {
		final StringBuilder sb = new StringBuilder();
		final Field[] fields = SMTFeature.class.getFields();
		final ArrayList<String> names = new ArrayList<>();
		for (final Field field : fields) {
			names.add(field.getName());
		}
		sb.append(String.join(delimiter, names));
		return sb.toString();
	}

	public static SMTFeature chooseLooser(final SMTFeature feature1, final SMTFeature feature2) {
		int score1 = 0;
		int score2 = 0;
		final String[] fieldnames = { "numberOfFunctions", "numberOfArrays", "dagsize", "numberOfVariables",
				"dependencyScore", "biggestEquivalenceClass", "numberOfSelectFunctions", "numberOfStoreFunctions" };
		for (final String fieldname : fieldnames) {
			int fieldvalue1 = 0;
			try {
				fieldvalue1 = (int) feature1.getClass().getField(fieldname).get(feature1);
			} catch (IllegalArgumentException | IllegalAccessException | NoSuchFieldException | SecurityException e) {
				e.printStackTrace();
			}
			int fieldvalue2 = 0;
			try {
				fieldvalue2 = (int) feature2.getClass().getField(fieldname).get(feature2);
			} catch (IllegalArgumentException | IllegalAccessException | NoSuchFieldException | SecurityException e) {
				e.printStackTrace();
			}
			if (fieldvalue1 < fieldvalue2) {
				score1 += 1;
			} else if (fieldvalue2 < fieldvalue1) {
				score2 += 1;
			}
		}

		if (score1 > score2) {
			return feature2;
		} else {
			return feature1;
		}
	}

}
