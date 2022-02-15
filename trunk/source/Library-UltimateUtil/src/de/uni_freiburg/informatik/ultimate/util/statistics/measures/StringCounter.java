/*
 * Copyright (C) 2022 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.statistics.measures;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class StringCounter {

	private final Map<String, Integer> mCounts = new LinkedHashMap<>();

	public void count(final Object obj) {
		count(obj.toString());
	}

	public void count(final String str) {
		mCounts.compute(str, (k, v) -> v == null ? 1 : v + 1);
	}

	public Map<String, Integer> getCounts() {
		return Collections.unmodifiableMap(mCounts);
	}

	@Override
	public String toString() {
		return mCounts.toString();
	}

	public static StringCounter aggregate(final Object o1, final Object o2) {
		final StringCounter c1 = (StringCounter) o1;
		final StringCounter c2 = (StringCounter) o2;
		final StringCounter rtr = new StringCounter();
		rtr.mCounts.putAll(c1.mCounts);
		c2.mCounts.entrySet()
				.forEach(a -> rtr.mCounts.compute(a.getKey(), (k, v) -> v == null ? a.getValue() : v + a.getValue()));
		return rtr;
	}

	public static boolean isEmpty(final Object o1) {
		final StringCounter c1 = (StringCounter) o1;
		return c1.mCounts.isEmpty();
	}

}
