/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.statistics.BenchmarkWithCounters;

public class HeapSeparatorBenchmark extends BenchmarkWithCounters {
	private final Set<ArrayGroup> mHeapArrayGroups = new HashSet<>();

	private final NestedMap3<ArrayGroup, Integer, HeapSeparatorStatistics, Number> mPerArrayAndDimensionInfo =
			new NestedMap3<>();

	private final NestedMap2<ArrayGroup, HeapSeparatorStatistics, Number> mPerArrayInfo = new NestedMap2<>();


	@Override
	protected void generateColumnTitlesAndResults() {
		if (mAlreadyGeneratedColumnTitlesAndResults) {
			return;
		}

		super.generateColumnTitlesAndResults();

		for (final ArrayGroup heapArrayGroup : mHeapArrayGroups) {
			for (int dim = 0; dim < heapArrayGroup.getDimensionality(); dim++) {
				for (final HeapSeparatorStatistics v : HeapSeparatorStatistics.values()) {
					// TODO group enum members..
					if (v == HeapSeparatorStatistics.COUNT_BLOCKS || v == HeapSeparatorStatistics.COUNT_ARRAY_WRITES) {
						mColumnTitles.add(v.name() + "_for_" + heapArrayGroup + "_at_dim_" + dim);
						mResults.add(mPerArrayAndDimensionInfo.get(heapArrayGroup, dim, v));
					}
				}
			}
		}

		for (final ArrayGroup heapArrayGroup : mHeapArrayGroups) {
			for (final HeapSeparatorStatistics v : HeapSeparatorStatistics.values()) {
				if (v == HeapSeparatorStatistics.COUNT_ARRAY_READS) {
					mColumnTitles.add(v.name() + " for " + heapArrayGroup);
					mResults.add(mPerArrayInfo.get(heapArrayGroup, v));
				}
			}
		}

//		mAlreadyGeneratedColumnTitlesAndResults = true; // done by super

	}

	void registerArrayGroup(final ArrayGroup ag) {
		final boolean newlyAdded = mHeapArrayGroups.add(ag);
		if (newlyAdded) {
			registerCounter(getNewArrayVarCounterName(ag));
		}
	}

	private String getNewArrayVarCounterName(final ArrayGroup ag) {
		return HeapSeparatorStatistics.COUNT_NEW_ARRAY_VARS.name() + "_" + ag;
	}

	void registerPerArrayInfo(final ArrayGroup ag, final HeapSeparatorStatistics hss, final Number value) {
		mPerArrayInfo.put(ag, hss, value);
	}

	void registerPerArrayAndDimensionInfo(final ArrayGroup ag, final int dim, final HeapSeparatorStatistics hss,
			final Number value) {
		mPerArrayAndDimensionInfo.put(ag, dim, hss, value);

	}

	@Override
	public String toString() {
		generateColumnTitlesAndResults();

		final StringBuilder sb = new StringBuilder();

		sb.append("\n");

		for (int i = 0; i < mColumnTitles.size(); i++) {
			sb.append(String.format("%-80s : %7d %n", mColumnTitles.get(i), mResults.get(i)));
		}
		return sb.toString();
	}

	public void incrementNewArrayVarCounter(final ArrayGroup arrayGroup) {
		super.incrementCounter(getNewArrayVarCounterName(arrayGroup));
	}

}
