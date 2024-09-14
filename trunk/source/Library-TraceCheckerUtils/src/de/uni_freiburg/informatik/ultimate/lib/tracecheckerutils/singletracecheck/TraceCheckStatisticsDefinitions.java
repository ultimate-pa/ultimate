/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

public enum TraceCheckStatisticsDefinitions implements IStatisticsElement {

	SsaConstructionTime(Long.class, StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY),

	SatisfiabilityAnalysisTime(Long.class, StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY),

	InterpolantComputationTime(Long.class, StatisticsType.LONG_ADDITION, StatisticsType.NANOS_BEFORE_KEY),

	NumberOfCodeBlocks(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	NumberOfCodeBlocksAsserted(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	NumberOfCheckSat(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	ConstructedInterpolants(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	QuantifiedInterpolants(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	SizeOfPredicates(Long.class, StatisticsType.LONG_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	NumberOfNonLiveVariables(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	ConjunctsInSsa(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	ConjunctsInUnsatCore(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	InterpolantComputations(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	PerfectInterpolantSequences(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	InterpolantCoveringCapability(BackwardCoveringInformation.class, CoverageAnalysis.DEFAULT_AGGREGATION,
			StatisticsType.DATA_BEFORE_KEY),

	// Test Case Generation Statistics:
	TraceChecks(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
	TestsExported(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
	ReusesTried(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
	InputVectorsExtended(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
	UNSAToptimizations(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

	SucessfullReuses(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA);

	private final Class<?> mClazz;
	private final Function<Object, Function<Object, Object>> mAggr;
	private final Function<String, Function<Object, String>> mPrettyprinter;

	TraceCheckStatisticsDefinitions(final Class<?> clazz, final Function<Object, Function<Object, Object>> aggr,
			final Function<String, Function<Object, String>> prettyprinter) {
		mClazz = clazz;
		mAggr = aggr;
		mPrettyprinter = prettyprinter;
	}

	@Override
	public Object aggregate(final Object o1, final Object o2) {
		return mAggr.apply(o1).apply(o2);
	}

	@Override
	public String prettyprint(final Object o) {
		return mPrettyprinter.apply(name()).apply(o);
	}
}
