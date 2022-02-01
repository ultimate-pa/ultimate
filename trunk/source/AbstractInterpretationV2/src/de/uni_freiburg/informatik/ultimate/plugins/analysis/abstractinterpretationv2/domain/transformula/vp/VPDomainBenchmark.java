/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BinaryOperator;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.VPStatistics;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class VPDomainBenchmark implements ICsvProviderProvider<Integer> {

	private int mLocationsCounter;
	private int mTransitionsCounter;

	private boolean mAlreadyGeneratedColumnTitlesAndResults = false;
	final private List<String> mColumnTitles = new ArrayList<>();
	final private List<Integer> mResults = new ArrayList<>();

	Map<VPStatistics, Integer> mLocationAggregateStatistics = new HashMap<>();
	Map<VPStatistics, Integer> mTransitionAggregateStatistics = new HashMap<>();


	@Override
	public ICsvProvider<Integer> createCsvProvider() {
		generateColumnTitlesAndResults();

		final ICsvProvider<Integer> result = new SimpleCsvProvider<>(mColumnTitles);
		result.addRow(mResults);

		return result;
	}

	protected void generateColumnTitlesAndResults() {
		if (mAlreadyGeneratedColumnTitlesAndResults) {
			return;
		}

		mColumnTitles.add("#Locations");
		mResults.add(mLocationsCounter);
		for (final VPStatistics stat : VPStatistics.values()) {
			mColumnTitles.add("LocStat_" + stat.toString());
			mResults.add(mLocationAggregateStatistics.get(stat));
		}

		mColumnTitles.add("#Transitions");
		mResults.add(mTransitionsCounter);
		for (final VPStatistics stat : VPStatistics.values()) {
			mColumnTitles.add("TransStat_" + stat.toString());
			mResults.add(mTransitionAggregateStatistics.get(stat));
		}


		mAlreadyGeneratedColumnTitlesAndResults = true;
	}

	public void setLocationsCounter(final int locationsCounter) {
		mLocationsCounter = locationsCounter;
	}

	public void setTransitionsCounter(final int transitionsCounter) {
		mTransitionsCounter = transitionsCounter;
	}

	@Override
	public String toString() {
		generateColumnTitlesAndResults();

		final StringBuilder sb = new StringBuilder();

		sb.append("\n");

		for (int i = 0; i < mColumnTitles.size(); i++) {
			sb.append(String.format("%-40s : %7d %n", mColumnTitles.get(i), mResults.get(i)));
		}
		return sb.toString();
	}

	public void reportStatsForLocation(final Function<VPStatistics, Integer> getStat) {
		for (final VPStatistics stat : VPStatistics.values()) {
			Integer currentVal = mLocationAggregateStatistics.get(stat);
			if (currentVal == null) {
				currentVal = VPStatistics.getInitialValue(stat);
			}
			final Integer valueForLoc = getStat.apply(stat);
			final BinaryOperator<Integer> agg = VPStatistics.getAggregator(stat);
			final Integer newVal = agg.apply(currentVal, valueForLoc);
			mLocationAggregateStatistics.put(stat, newVal);
		}
	}

	public void reportStatsForTransitionRelation(final Function<VPStatistics, Integer> getStat) {
		for (final VPStatistics stat : VPStatistics.values()) {
			Integer currentVal = mTransitionAggregateStatistics.get(stat);
			if (currentVal == null) {
				currentVal = VPStatistics.getInitialValue(stat);
			}
			final Integer valueForLoc = getStat.apply(stat);
			final BinaryOperator<Integer> agg = VPStatistics.getAggregator(stat);
			final Integer newVal = agg.apply(currentVal, valueForLoc);
			mTransitionAggregateStatistics.put(stat, newVal);
		}
	}
}

