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

import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.util.statistics.measures.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

/**
 * Functions to aggregate measures defined by a {@link MeasureDefinition}. You probably want to use these functions as
 * references (for instance {@code BiFunction<Object, Object, Object> aggr = Aggregate::intAdd}) instead of calling them
 * directly.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 */
public final class Aggregate {

	private Aggregate() {
		// objects of this class have no use ==> forbid construction
	}

	public static StatisticsAggregator statisticsConvertAndAggregate(final Object lhs, final Object rhs) {
		final StatisticsAggregator rtr = createStatisticsAggregator(lhs, rhs);
		rtr.aggregateStatisticsData((IStatisticsDataProvider) lhs);
		rtr.aggregateStatisticsData((IStatisticsDataProvider) rhs);
		return rtr;
	}

	private static StatisticsAggregator createStatisticsAggregator(final Object o1, final Object o2) {
		if (o1 instanceof BaseStatisticsDataProvider) {
			return new StatisticsAggregator((BaseStatisticsDataProvider) o1);
		}
		if (o2 instanceof BaseStatisticsDataProvider) {
			return new StatisticsAggregator((BaseStatisticsDataProvider) o2);
		}
		return new StatisticsAggregator();
	}

	public static StatisticsAggregator statisticsAggregator(final Object lhs, final Object rhs) {
		final StatisticsAggregator rtr;
		if (lhs instanceof StatisticsAggregator) {
			rtr = (StatisticsAggregator) lhs;
			rtr.aggregateStatisticsData((IStatisticsDataProvider) rhs);
			return rtr;
		}
		rtr = createStatisticsAggregator(lhs, rhs);
		rtr.aggregateStatisticsData((IStatisticsDataProvider) lhs);
		rtr.aggregateStatisticsData((IStatisticsDataProvider) rhs);
		return rtr;
	}

	public static List<Object> appendList(final Object lhsList, final Object rhsList) {
		((List<Object>) lhsList).addAll((Collection<Object>) rhsList);
		return (List<Object>) lhsList;
	}

	public static Integer intAdd(final Object lhsInt, final Object rhsInt) {
		return (int) lhsInt + (int) rhsInt;
	}

	public static int[] intArrayAddElementWise(final Object lhs, final Object rhs) {
		final int[] lhsA = (int[]) lhs;
		final int[] rhsA = (int[]) rhs;
		if (lhsA.length != rhsA.length) {
			throw new IllegalArgumentException("Arrays have to be the same length");
		}
		final int[] rtr = new int[lhsA.length];
		for (int i = 0; i < rtr.length; ++i) {
			rtr[i] = lhsA[i] + rhsA[i];
		}
		return rtr;
	}

	public static Integer intMax(final Object lhsInt, final Object rhsInt) {
		return Math.max((int) lhsInt, (int) rhsInt);
	}

	public static Long longAdd(final Object lhsLong, final Object rhsLong) {
		return (long) lhsLong + (long) rhsLong;
	}

	public static Long longMax(final Object lhsLong, final Object rhsLong) {
		return Math.max((long) lhsLong, (long) rhsLong);
	}

	public static Double doubleAdd(final Object lhsDouble, final Object rhsDouble) {
		return (double) lhsDouble + (double) rhsDouble;
	}

	public static InCaReCounter inCaReAdd(final Object lhsInCaRe, final Object rhsInCaRe) {
		((InCaReCounter) lhsInCaRe).add((InCaReCounter) rhsInCaRe);
		return (InCaReCounter) lhsInCaRe;
	}

	public static TimeTracker timeTrackerAdd(final Object lhs, final Object rhs) {
		final TimeTracker tt = new TimeTracker();
		tt.addElapsedTime(((TimeTracker) lhs).elapsedTime(TimeUnit.NANOSECONDS));
		tt.addElapsedTime(((TimeTracker) rhs).elapsedTime(TimeUnit.NANOSECONDS));
		return tt;
	}

	public static TimeTracker timeTrackerMax(final Object lhs, final Object rhs) {
		final long lhsEl = ((TimeTracker) lhs).elapsedTime(TimeUnit.NANOSECONDS);
		final long rhsEl = ((TimeTracker) rhs).elapsedTime(TimeUnit.NANOSECONDS);

		final TimeTracker tt = new TimeTracker();
		tt.addElapsedTime(Math.max(lhsEl, rhsEl));
		return tt;
	}

	public static Boolean flagAnd(final Object lhs, final Object rhs) {
		final Boolean lhsC = (Boolean) lhs;
		final Boolean rhsC = (Boolean) rhs;

		if (null == lhsC) {
			return rhsC;
		}
		if (null == rhsC) {
			return lhsC;
		}
		return lhsC && rhsC;
	}

}
