/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.statistics;

import java.util.EnumMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.MeasureDefinition;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

/**
 * Statistics for Sifa.
 * <p>
 * Sifa doesn't use the Ultimate's common statistics classes as intended as we would have to create and return new
 * statistics objects at too many places. In Sifa there is only one statistics object which does <i>not</i> use the
 * aggregation functions. Aggregation is done in-place inside the statistics object. This is not pretty, but prettier
 * than the alternative of returning a pair (actual result + statistics) at every other function.
 * <p>
 * Stopwatches in this class can be nested like parenthesis, that is stopwatch {@code s} can be used as in
 * {@code start(s); start(s); stop(s); stop(s);}. The measured time is the time between the first {@code start} and its
 * corresponding {@code stop}.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class SifaStats extends BaseStatisticsDataProvider {

	private final Map<SifaMeasures, Integer> mStopwatchNestingLevels = new EnumMap<>(SifaMeasures.class);
	private final Map<SifaMeasures, Integer> mIntCounters = new EnumMap<>(SifaMeasures.class);
	private final Map<SifaMeasures, MaxTimerData> mMaxTimerData = new EnumMap<>(SifaMeasures.class);
	private final Map<SifaMeasures, TimeTracker> mStopWatches = new EnumMap<>(SifaMeasures.class);

	public SifaStats(final IToolchainStorage storage) {
		super(storage);

		for (final SifaMeasures k : SifaMeasures.values()) {
			final Supplier<Object> getter;
			if (k.isStopwatch()) {
				getter = () -> valueOfStopwatch(k);
			} else if (k.isMaxTimer()) {
				getter = () -> mMaxTimerData.computeIfAbsent(k, key -> new MaxTimerData()).mMaxTime;
			} else {
				getter = () -> valueOfIntCounter(k);
			}
			declare(k.name(), getter, k.getType());
		}

	}

	public void start(final SifaMeasures stopwatchId) {
		final int nestingLevel = mStopwatchNestingLevels.getOrDefault(stopwatchId, 0);
		if (nestingLevel == 0) {
			// without .name() we recurse endlessly
			getTimeTracker(stopwatchId).start();
		} else if (nestingLevel < 0) {
			throw new IllegalStateException("Negative nesting level for stopwatch " + stopwatchId);
		}
		mStopwatchNestingLevels.put(stopwatchId, nestingLevel + 1);
	}

	public void stop(final SifaMeasures stopwatchId) {
		final int nestingLevel = mStopwatchNestingLevels.getOrDefault(stopwatchId, 0);
		if (nestingLevel == 1) {
			// without .name() we recurse endlessly
			getTimeTracker(stopwatchId).stop();
		} else if (nestingLevel < 1) {
			throw new IllegalStateException("Called stop() without start() for stopwatch " + stopwatchId);
		}
		mStopwatchNestingLevels.put(stopwatchId, nestingLevel - 1);
	}

	public void startMax(final SifaMeasures stopwatchId) {
		start(stopwatchId);
	}

	public void stopMax(final SifaMeasures stopwatchId) {
		stop(stopwatchId);
		final long totalTime = valueOfStopwatch(stopwatchId);
		final MaxTimerData old = mMaxTimerData.computeIfAbsent(stopwatchId, key -> new MaxTimerData());
		old.mMaxTime = Math.max(old.mMaxTime, totalTime - old.mTotalTime);
		old.mTotalTime = totalTime;
	}

	private TimeTracker getTimeTracker(final SifaMeasures id) {
		return mStopWatches.computeIfAbsent(id, this::createTimeTracker);
	}

	private TimeTracker createTimeTracker(final SifaMeasures id) {
		return new TimeTracker();
	}

	public Object getValue(final SifaMeasures keyId) {
		if (keyId.isMaxTimer()) {
			return mMaxTimerData.computeIfAbsent(keyId, key -> new MaxTimerData()).mMaxTime;
		}
		if (keyId.isStopwatch()) {
			return valueOfStopwatch(keyId);
		}
		return valueOfIntCounter(keyId);
	}

	private Long valueOfStopwatch(final SifaMeasures stopwatchId) {
		return getTimeTracker(stopwatchId).elapsedTime(TimeUnit.NANOSECONDS);
	}

	private Integer valueOfIntCounter(final SifaMeasures intCounterId) {
		return mIntCounters.getOrDefault(intCounterId, 0);
	}

	public void increment(final SifaMeasures intCounterId) {
		add(intCounterId, 1);
	}

	public void add(final SifaMeasures intCounterId, final int summand) {
		mIntCounters.put(intCounterId, mIntCounters.getOrDefault(intCounterId, 0) + summand);
	}

	public enum SifaMeasures {
		OVERALL_TIME(MeasureDefinition.LONG_TIME),

		/** Number of procedures entered (excluding CallReturnSummaries) during interpretation of the icfg. */
		ICFG_INTERPRETER_ENTERED_PROCEDURES(MeasureDefinition.INT_COUNTER),

		DAG_INTERPRETER_EARLY_EXIT_QUERIES_NONTRIVIAL(MeasureDefinition.INT_COUNTER),

		DAG_INTERPRETER_EARLY_EXITS(MeasureDefinition.INT_COUNTER),

		TOOLS_POST_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		TOOLS_POST_TIME(MeasureDefinition.LONG_TIME),

		TOOLS_POST_CALL_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		TOOLS_POST_CALL_TIME(MeasureDefinition.LONG_TIME),

		TOOLS_POST_RETURN_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		TOOLS_POST_RETURN_TIME(MeasureDefinition.LONG_TIME),

		TOOLS_QUANTIFIERELIM_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		TOOLS_QUANTIFIERELIM_TIME(MeasureDefinition.LONG_TIME),

		TOOLS_QUANTIFIERELIM_MAX_TIME(MeasureDefinition.LONG_TIME_MAX),

		/** Overall time spent answering queries. */
		FLUID_QUERY_TIME(MeasureDefinition.LONG_TIME),
		/** Number of queries to fluid. */
		FLUID_QUERIES(MeasureDefinition.INT_COUNTER),
		/** Number of queries to fluid answered with "yes, abstract the state". */
		FLUID_YES_ANSWERS(MeasureDefinition.INT_COUNTER),

		DOMAIN_JOIN_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		DOMAIN_JOIN_TIME(MeasureDefinition.LONG_TIME),

		DOMAIN_ALPHA_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		DOMAIN_ALPHA_TIME(MeasureDefinition.LONG_TIME),

		DOMAIN_WIDEN_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		DOMAIN_WIDEN_TIME(MeasureDefinition.LONG_TIME),

		DOMAIN_ISSUBSETEQ_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		DOMAIN_ISSUBSETEQ_TIME(MeasureDefinition.LONG_TIME),

		DOMAIN_ISBOTTOM_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		DOMAIN_ISBOTTOM_TIME(MeasureDefinition.LONG_TIME),

		LOOP_SUMMARIZER_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		LOOP_SUMMARIZER_CACHE_MISSES(MeasureDefinition.INT_COUNTER),
		/**
		 * Time spent to obtain loop summaries, including the time to look search the cache and re-use existing
		 * summaries.
		 */
		LOOP_SUMMARIZER_OVERALL_TIME(MeasureDefinition.LONG_TIME),
		/** Time spent to compute completely new loop summaries in case of cache misses. */
		LOOP_SUMMARIZER_NEW_COMPUTATION_TIME(MeasureDefinition.LONG_TIME),
		/** Overall number of iterations. This statistic is specific to FixpointLoopSummerizer. */
		LOOP_SUMMARIZER_FIXPOINT_ITERATIONS(MeasureDefinition.INT_COUNTER),

		CALL_SUMMARIZER_APPLICATIONS(MeasureDefinition.INT_COUNTER),

		CALL_SUMMARIZER_CACHE_MISSES(MeasureDefinition.INT_COUNTER),
		/**
		 * Time spent to obtain call summaries, including the time to look search the cache and re-use existing
		 * summaries.
		 */
		CALL_SUMMARIZER_OVERALL_TIME(MeasureDefinition.LONG_TIME),
		/** Time spent to compute completely new call summaries in case of cache misses. */
		CALL_SUMMARIZER_NEW_COMPUTATION_TIME(MeasureDefinition.LONG_TIME),

		PROCEDURE_GRAPH_BUILDER_TIME(MeasureDefinition.LONG_TIME),

		/** Time spent computing path expressions (= regexes) from graphs. */
		PATH_EXPR_TIME(MeasureDefinition.LONG_TIME),

		/** Time spent converting regexes into dags. */
		REGEX_TO_DAG_TIME(MeasureDefinition.LONG_TIME),

		/** Time spent compressing RegexDags. This can include multiple compression runs on different dags. */
		DAG_COMPRESSION_TIME(MeasureDefinition.LONG_TIME),
		/** Sum of number of nodes in processed RegexDags before compression. */
		DAG_COMPRESSION_PROCESSED_NODES(MeasureDefinition.INT_COUNTER),
		/** Sum of number of nodes in processed RegexDags after compression. */
		DAG_COMPRESSION_RETAINED_NODES(MeasureDefinition.INT_COUNTER),;

		private final MeasureDefinition mType;

		SifaMeasures(final MeasureDefinition type) {
			mType = type;
		}

		public MeasureDefinition getType() {
			return mType;
		}

		public boolean isMaxTimer() {
			return getType() == MeasureDefinition.LONG_TIME_MAX;
		}

		public boolean isStopwatch() {
			return getType() == MeasureDefinition.LONG_TIME || getType() == MeasureDefinition.LONG_TIME_MAX;
		}
	}

	private static class MaxTimerData {
		private long mTotalTime;
		private long mMaxTime;
	}
}
