/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

public class CegarStatisticsType extends StatisticsType<CegarLoopStatisticsDefinitions> {

	public static final Function<Object, Function<Object, Object>> SIZE_ITERATION_PAIR_DATA_AGGREGATION = x -> y -> {
		return ((SizeIterationPair) x).getSize() >= ((SizeIterationPair) y).getSize() ? x : y;
	};

	public CegarStatisticsType() {
		super(CegarLoopStatisticsDefinitions.class);
	}

	private static final CegarStatisticsType INSTANCE = new CegarStatisticsType();

	public static CegarStatisticsType getInstance() {
		return INSTANCE;
	}

	public static String prettyprintNanoseconds(final long time) {
		final long seconds = time / 1000000000;
		final long tenthDigit = time / 100000000 % 10;
		return seconds + "." + tenthDigit + "s";
	}

	public String prettyprintBenchmarkDataNoStopWatch(final IStatisticsDataProvider benchmarkData,
			final boolean noStopwatch) {
		return prettyprintBenchmarkData(getKeys(), benchmarkData, noStopwatch);
	}

	@Override
	public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
		return prettyprintBenchmarkData(getKeys(), benchmarkData, false);
	}

	public static <T extends Enum<T> & IStatisticsElement> String prettyprintBenchmarkData(
			final Collection<String> keys, final IStatisticsDataProvider benchmarkData, final boolean noStopwatch) {
		final StringBuilder sb = new StringBuilder();
		String delimiter = "";
		for (final String key : keys) {
			sb.append(delimiter);

			final CegarLoopStatisticsDefinitions keyE = Enum.valueOf(CegarLoopStatisticsDefinitions.class, key);
			switch (keyE) {
			case OverallTime:
			case EmptinessCheckTime:
			case AutomataDifference:
			case DeadEndRemovalTime:
			case HoareAnnotationTime:
			case BasicInterpolantAutomatonTime:
			case InitialAbstractionConstructionTime:
			case DumpTime:
				if (noStopwatch) {
					break;
				}
			default:
				final Object value = benchmarkData.getValue(key);
				sb.append(keyE.prettyprint(value));
				delimiter = ", ";
			}

		}
		return sb.toString();

	}

	public static class SizeIterationPair {
		final int mSize;
		final int mIteration;

		public SizeIterationPair(final int size, final int iteration) {
			super();
			mSize = size;
			mIteration = iteration;
		}

		public int getSize() {
			return mSize;
		}

		public int getIteration() {
			return mIteration;
		}

		@Override
		public String toString() {
			return "size=" + mSize + "occurred in iteration=" + mIteration;
		}
	}
}
