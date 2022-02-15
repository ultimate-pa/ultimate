/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization;

import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.Reflected;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsAggregator;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

public class ErrorLocalizationStatisticsGenerator extends BaseStatisticsDataProvider {

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mSuccesfullyFinished;

	@Reflected(prettyName = "Error Localization Time")
	@Statistics(type = DefaultMeasureDefinitions.TT_TIMER)
	private final TimeTracker mTime;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mIcfgEdges;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mErrorEnforcingIcfgEdges;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mErrorAdmittingIcfgEdges;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mErrorIrrelevantIcfgEdges;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private int mNumberOfBranches;

	@Statistics(type = DefaultMeasureDefinitions.DOUBLE_COUNTER)
	private double mAngelicScore;

	@Reflected(prettyName = "Error Localization Htc")
	@Statistics(type = DefaultMeasureDefinitions.STATISTICS_AGGREGATOR)
	private final StatisticsAggregator mHoareTripleCheckerStatistics;

	public ErrorLocalizationStatisticsGenerator(final IToolchainStorage storage) {
		super(storage);
		mTime = new TimeTracker();
		mHoareTripleCheckerStatistics = new StatisticsAggregator(storage);
	}

	public long getErrorLocalizationTime() {
		return mTime.elapsedTime(TimeUnit.NANOSECONDS);
	}

	public void startTime() {
		mTime.start();
	}

	public void stopTime() {
		mTime.stop();
	}

	public void reportSuccesfullyFinished() {
		if (mSuccesfullyFinished > 0) {
			throw new IllegalStateException("already finished before");
		}
		mSuccesfullyFinished++;
	}

	public void reportIcfgEdge() {
		mIcfgEdges++;
	}

	public void reportErrorEnforcingIcfgEdge() {
		mErrorEnforcingIcfgEdges++;
	}

	public void reportErrorAdmittingIcfgEdge() {
		mErrorAdmittingIcfgEdges++;
	}

	public void reportErrorIrrelevantIcfgEdge() {
		mErrorIrrelevantIcfgEdges++;
	}

	public void reportNumberOfBranches(final int numberOfBranches) {
		mNumberOfBranches = numberOfBranches;
	}

	public void reportAngelicScore(final double angelicScore) {
		mAngelicScore = angelicScore;
	}

	public void
			addHoareTripleCheckerStatistics(final HoareTripleCheckerStatisticsGenerator hoareTripleCheckerStatistics) {
		mHoareTripleCheckerStatistics.aggregateStatisticsData(hoareTripleCheckerStatistics);
	}
}
