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

import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Functions to pretty print statistics defined by a single {@link IStatisticsElement}. You probably want to use these
 * functions as references (for instance {@code BiFunction<String, Object, String> pprint = PrettyPrint::dataThenKey})
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

	/**
	 * Wraps another pretty printer to represent time data (given as nano seconds) in a way such that the user can
	 * recognize the data as time.
	 *
	 * @param pprinter
	 *            Pretty printer to be wrapped
	 * @return Pretty printer printing times by interpreting the data as nano seconds first
	 */
	public static BiFunction<String, Object, String> dataAsTime(final BiFunction<String, Object, String> pprinter) {
		// having the unit in the field name rather than in the data makes processing easier
		return (key, data) -> pprinter.apply(key,
				CoreUtil.toTimeString((long) data, TimeUnit.NANOSECONDS, TimeUnit.SECONDS, 1));
	}

	public static BiFunction<String, Object, String>
			dataAsTimeMilli(final BiFunction<String, Object, String> pprinter) {
		return (key, data) -> pprinter.apply(key,
				CoreUtil.toTimeString((long) data, TimeUnit.NANOSECONDS, TimeUnit.MILLISECONDS, 1));
	}

	public static BiFunction<String, Object, String> list(final BiFunction<String, Object, String> pprinter,
			final Function<Object, String> elemPrinter) {
		return (key, data) -> pprinter.apply(key,
				((List) data).stream().map(elemPrinter).collect(Collectors.joining(", ", "[ ", " ]")));
	}

}
