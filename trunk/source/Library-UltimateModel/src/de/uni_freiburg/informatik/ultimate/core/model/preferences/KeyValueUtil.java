/*
 * Copyright (C) 2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE GUIGeneratedPreferencePages plug-in.
 *
 * The ULTIMATE GUIGeneratedPreferencePages plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE GUIGeneratedPreferencePages plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE GUIGeneratedPreferencePages plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE GUIGeneratedPreferencePages plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE GUIGeneratedPreferencePages plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.model.preferences;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

/**
 * Small utility that supports the {@link PreferenceType#KeyValue}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class KeyValueUtil {

	private static final String PAIR_SEPARATOR = ";";
	private static final String KV_SEPARATOR = "=";

	private KeyValueUtil() {
		// utility class should not be instantiated
	}

	/**
	 * Convert a map to a single line String of the form "key0=value0;key1=value1;..."
	 */
	public static String toKeyValueString(final Map<String, String> map) {
		final StringBuilder sb = new StringBuilder();
		for (final Entry<String, String> entry : map.entrySet()) {
			final String key = check(entry.getKey());
			final String value = check(entry.getValue());

			sb.append(key).append(KV_SEPARATOR).append(value).append(PAIR_SEPARATOR);
		}
		return sb.toString();
	}

	private static String check(final String s) {
		if (s == null) {
			throw new IllegalArgumentException("Key or value cannot be null");
		}
		if (s.contains(PAIR_SEPARATOR)) {
			throw new IllegalArgumentException(String.format("Key or value cannot contain %s", PAIR_SEPARATOR));
		}
		if (s.contains(KV_SEPARATOR)) {
			throw new IllegalArgumentException(String.format("Key or value cannot contain %s", KV_SEPARATOR));
		}
		return s;
	}

	/**
	 * Convert a String of the form "key0=value0;key1=value1;..." to a map. If the string contains duplicate keys, the
	 * last occurrence will be saved.
	 */
	public static Map<String, String> toMap(final String str) {
		if (str == null || str.isEmpty()) {
			return new LinkedHashMap<>();
		}

		final String[] keyvaluepairs = str.split(PAIR_SEPARATOR);

		if (keyvaluepairs == null || keyvaluepairs.length == 0) {
			return new LinkedHashMap<>();
		}
		final Map<String, String> rtr = new LinkedHashMap<>();
		for (final String pair : keyvaluepairs) {
			if (KV_SEPARATOR.equals(pair)) {
				rtr.put("", "");
				continue;
			}
			final String[] kvp = pair.split(KV_SEPARATOR);
			if (kvp.length != 2) {
				throw new IllegalArgumentException(String.format("String %s is not of the form key=value", pair));
			}
			rtr.put(kvp[0], kvp[1]);
		}
		return rtr;
	}

	/**
	 * Assumes each entry represents a key value pair of the form "key=value"
	 */
	public static String toKeyValueString(final Object[] values) {
		final StringBuilder sb = new StringBuilder();
		for (final Object val : values) {
			final String[] kvp = String.valueOf(val).split(KV_SEPARATOR);
			if (kvp.length == 0) {
				sb.append(KV_SEPARATOR).append(PAIR_SEPARATOR);
				continue;
			}
			if (kvp.length == 2) {
				sb.append(check(kvp[0])).append(KV_SEPARATOR).append(check(kvp[1])).append(PAIR_SEPARATOR);
				continue;
			}
			throw new IllegalArgumentException(String.format("Object %s is not of the form key=value", val));
		}
		return sb.toString();
	}

	public static boolean isValid(final String s) {
		if (s == null) {
			return false;
		}
		if (s.contains(PAIR_SEPARATOR)) {
			return false;
		}
		if (s.contains(KV_SEPARATOR)) {
			return false;
		}
		return true;
	}

	public static boolean isValid(final Entry<String, String> entry) {
		return isValid(entry.getKey()) && isValid(entry.getValue());
	}

}
