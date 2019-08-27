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

import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;

/**
 * Functions to aggregate statistics defined by a single {@link IStatisticsElement}.
 * You probably want to use these functions as references (for instance
 * {@code BiFunction<Object, Object, Object> aggr = Aggregate::intAdd})
 * instead of calling them directly.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public final class Aggregate {

	private Aggregate() {
		// objects of this class have no use ==> forbid construction
	}

	public static StatisticsData statisticsDataAggregate(final Object lhsStatsData, final Object rhsStatsData) {
		((StatisticsData) lhsStatsData).aggregateBenchmarkData((StatisticsData) rhsStatsData);
		return (StatisticsData) lhsStatsData;
	}

	public static Integer intAdd(final Object lhsInt, final Object rhsInt) {
		return (int) lhsInt + (int) rhsInt;
	}

	public static Integer intMax(final Object lhsInt, final Object rhsInt) {
		return Math.max((int) lhsInt, (int) rhsInt);
	}

	public static Long longAdd(final Object lhsLong, final Object rhsLong) {
		return (long) lhsLong + (long) rhsLong;
	}

	public static Double doubleAdd(final Object lhsDouble, final Object rhsDouble) {
		return (double) lhsDouble + (double) rhsDouble;
	}

	public static InCaReCounter inCaReAdd(final Object lhsInCaRe, final Object rhsInCaRe) {
		((InCaReCounter) lhsInCaRe).add((InCaReCounter) rhsInCaRe);
		return (InCaReCounter) lhsInCaRe;
	}

}
