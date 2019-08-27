/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.util.Locale;

/**
 * Functions to pretty print statistics defined by a single {@link IStatisticsElement}.
 * You probably want to use these functions as references (for instance
 * {@code BiFunction<String, Object, String> pprint = PrettyPrint::dataThenKey})
 * instead of calling them directly.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public final class PrettyPrint {

	private PrettyPrint() {
		// objects of this class have no use ==> forbid construction
	}

	public static String dataSpaceKey(final String key, final Object data) {
		return String.format("%s %s", data, key);
	}

	public static String keyColonData(final String key, final Object data) {
		return String.format("%s: %s", key, data);
	}

	public static String timeFromNanosSpaceKey(final String key, final Object longData) {
		return String.format("%s %s", nanosToTime(longData), key);
	}

	public static String keyColonTimeFromNanos(final String key, final Object longData) {
		return String.format("%s: %s", key, nanosToTime(longData));
	}

	private static String nanosToTime(final Object nanosAsLong) {
		return String.format(Locale.US, "%.1fs", (long) nanosAsLong / 1e9);
	}
}
