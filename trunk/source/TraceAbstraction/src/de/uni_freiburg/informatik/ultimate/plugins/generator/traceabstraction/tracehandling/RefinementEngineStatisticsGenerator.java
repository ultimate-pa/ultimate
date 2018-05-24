/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation.InterpolantConsolidationBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckPathInvariantsWithFallback;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public class RefinementEngineStatisticsGenerator implements IStatisticsDataProvider {

	private final StatisticsData mTraceCheckStatistics = new StatisticsData();
	private final StatisticsData mInvariantSynthesisStatistics = new StatisticsData();
	private final StatisticsData mInterpolantConsolidationStatistics = new StatisticsData();

	@Override
	public IStatisticsType getBenchmarkType() {
		return RefinementEngineStatisticsType.getInstance();
	}

	private void addTraceCheckStatistics(final IStatisticsDataProvider traceCheckStatistics) {
		mTraceCheckStatistics.aggregateBenchmarkData(traceCheckStatistics);
	}

	private void addInvariantSynthesisStatistics(final IStatisticsDataProvider invariantSynthesisStatistics) {
		mInvariantSynthesisStatistics.aggregateBenchmarkData(invariantSynthesisStatistics);
	}

	public void addInterpolantConsolidationStatistics(
			final InterpolantConsolidationBenchmarkGenerator interpolantConsolidationStatistics) {
		mInterpolantConsolidationStatistics.aggregateBenchmarkData(interpolantConsolidationStatistics);
	}

	public void addTraceCheckStatistics(final ITraceCheck traceCheck) {
		if (!traceCheck.wasTracecheckFinishedNormally()) {
			return;
		}
		addTraceCheckStatistics(traceCheck.getTraceCheckBenchmark());
		if (traceCheck instanceof InterpolatingTraceCheckPathInvariantsWithFallback
				&& traceCheck.isCorrect() == LBool.UNSAT) {
			addInvariantSynthesisStatistics(
					((InterpolatingTraceCheckPathInvariantsWithFallback<?>) traceCheck).getPathInvariantsStats());
		}
	}

	@Override
	public Object getValue(final String key) {
		final RefinementEngineStatisticsDefinitions keyEnum =
				Enum.valueOf(RefinementEngineStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case InterpolantConsolidationStatistics:
			return mInterpolantConsolidationStatistics;
		case InvariantSynthesisStatistics:
			return mInvariantSynthesisStatistics;
		case TraceCheckStatistics:
			return mTraceCheckStatistics;
		default:
			throw new AssertionError("unknown data");
		}
	}

	@Override
	public Collection<String> getKeys() {
		return RefinementEngineStatisticsType.getInstance().getKeys();
	}

}