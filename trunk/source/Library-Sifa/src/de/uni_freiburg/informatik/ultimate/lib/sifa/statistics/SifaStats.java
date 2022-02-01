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

import java.util.Arrays;
import java.util.Collection;
import java.util.EnumMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.statistics.IKeyedStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

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
public class SifaStats extends StatisticsGeneratorWithStopwatches implements IStatisticsDataProvider {

	private static final StatisticsType<Key> TYPE = new StatisticsType<>(Key.class);

	private final Map<Key, Integer> mStopwatchNestingLevels = new EnumMap<>(Key.class);
	private final Map<Key, Integer> mIntCounters = new EnumMap<>(Key.class);
	private final Map<Key, MaxTimerData> mMaxTimerData = new EnumMap<>(Key.class);

	@Override
	public void start(final String stopwatchName) {
		start(Key.valueOf(stopwatchName));
	}

	public void start(final Key stopwatchId) {
		final int nestingLevel = mStopwatchNestingLevels.getOrDefault(stopwatchId, 0);
		if (nestingLevel == 0) {
			// without .name() we recurse endlessly
			super.start(stopwatchId.name());
		} else if (nestingLevel < 0) {
			throw new IllegalStateException("Negative nesting level for stopwatch " + stopwatchId);
		}
		mStopwatchNestingLevels.put(stopwatchId, nestingLevel + 1);
	}

	@Override
	public void stop(final String stopwatchName) {
		stop(Key.valueOf(stopwatchName));
	}

	public void stop(final Key stopwatchId) {
		final int nestingLevel = mStopwatchNestingLevels.getOrDefault(stopwatchId, 0);
		if (nestingLevel == 1) {
			// without .name() we recurse endlessly
			super.stop(stopwatchId.name());
		} else if (nestingLevel < 1) {
			throw new IllegalStateException("Called stop() without start() for stopwatch " + stopwatchId);
		}
		mStopwatchNestingLevels.put(stopwatchId, nestingLevel - 1);
	}

	public void startMax(final Key stopwatchId) {
		start(stopwatchId);
	}

	public void stopMax(final Key stopwatchId) {
		stop(stopwatchId);
		final long totalTime;
		try {
			totalTime = getElapsedTime(stopwatchId.name());
		} catch (final StopwatchStillRunningException e) {
			// support nesting only when needed -- at the moment we don't need it
			throw new AssertionError("Clock still runing after it was stopped. Nesting MaxTimers not supported yet.");
		}
		final MaxTimerData old = mMaxTimerData.computeIfAbsent(stopwatchId, key -> new MaxTimerData());
		old.mMaxTime = Math.max(old.mMaxTime, totalTime - old.mTotalTime);
		old.mTotalTime = totalTime;
	}

	@Override
	public Object getValue(final String keyName) {
		return getValue(Key.valueOf(keyName));
	}

	public Object getValue(final Key keyId) {
		if (keyId.isMaxTimer()) {
			return mMaxTimerData.computeIfAbsent(keyId, key -> new MaxTimerData()).mMaxTime;
		} else if (keyId.isStopwatch()) {
			return valueOfStopwatch(keyId);
		} else {
			return valueOfIntCounter(keyId);
		}
	}

	private Long valueOfStopwatch(final Key stopwatchId) {
		try {
			return getElapsedTime(stopwatchId.name());
		} catch (final StopwatchStillRunningException stillRunning) {
			throw new AssertionError(stillRunning);
		}
	}

	private Integer valueOfIntCounter(final Key intCounterId) {
		return mIntCounters.getOrDefault(intCounterId, 0);
	}

	public void increment(final Key intCounterId) {
		add(intCounterId, 1);
	}

	public void add(final Key intCounterId, final int summand) {
		mIntCounters.put(intCounterId, mIntCounters.getOrDefault(intCounterId, 0) + summand);
	}

	@Override
	public Collection<String> getKeys() {
		return TYPE.getKeys();
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return TYPE;
	}

	@Override
	public String[] getStopwatches() {
		// TODO add max timers
		return Arrays.stream(Key.values()).filter(Key::isStopwatch).map(Enum::name).toArray(String[]::new);
	}

	public enum Key implements IKeyedStatisticsElement {
		OVERALL_TIME(KeyType.TIMER),

		/** Number of procedures entered (excluding CallReturnSummaries) during interpretation of the icfg. */
		ICFG_INTERPRETER_ENTERED_PROCEDURES(KeyType.COUNTER),

		DAG_INTERPRETER_EARLY_EXIT_QUERIES_NONTRIVIAL(KeyType.COUNTER),

		DAG_INTERPRETER_EARLY_EXITS(KeyType.COUNTER),

		TOOLS_POST_APPLICATIONS(KeyType.COUNTER),

		TOOLS_POST_TIME(KeyType.TIMER),

		TOOLS_POST_CALL_APPLICATIONS(KeyType.COUNTER),

		TOOLS_POST_CALL_TIME(KeyType.TIMER),

		TOOLS_POST_RETURN_APPLICATIONS(KeyType.COUNTER),

		TOOLS_POST_RETURN_TIME(KeyType.TIMER),

		TOOLS_QUANTIFIERELIM_APPLICATIONS(KeyType.COUNTER),

		TOOLS_QUANTIFIERELIM_TIME(KeyType.TIMER),

		TOOLS_QUANTIFIERELIM_MAX_TIME(KeyType.MAX_TIMER),

		/** Overall time spent answering queries. */
		FLUID_QUERY_TIME(KeyType.TIMER),
		/** Number of queries to fluid. */
		FLUID_QUERIES(KeyType.COUNTER),
		/** Number of queries to fluid answered with "yes, abstract the state". */
		FLUID_YES_ANSWERS(KeyType.COUNTER),

		DOMAIN_JOIN_APPLICATIONS(KeyType.COUNTER),

		DOMAIN_JOIN_TIME(KeyType.TIMER), DOMAIN_ALPHA_APPLICATIONS(KeyType.COUNTER),

		DOMAIN_ALPHA_TIME(KeyType.TIMER), DOMAIN_WIDEN_APPLICATIONS(KeyType.COUNTER),

		DOMAIN_WIDEN_TIME(KeyType.TIMER), DOMAIN_ISSUBSETEQ_APPLICATIONS(KeyType.COUNTER),

		DOMAIN_ISSUBSETEQ_TIME(KeyType.TIMER), DOMAIN_ISBOTTOM_APPLICATIONS(KeyType.COUNTER),

		DOMAIN_ISBOTTOM_TIME(KeyType.TIMER),

		LOOP_SUMMARIZER_APPLICATIONS(KeyType.COUNTER),

		LOOP_SUMMARIZER_CACHE_MISSES(KeyType.COUNTER),
		/**
		 * Time spent to obtain loop summaries, including the time to look search the cache and re-use existing
		 * summaries.
		 */
		LOOP_SUMMARIZER_OVERALL_TIME(KeyType.TIMER),
		/** Time spent to compute completely new loop summaries in case of cache misses. */
		LOOP_SUMMARIZER_NEW_COMPUTATION_TIME(KeyType.TIMER),
		/** Overall number of iterations. This statistic is specific to FixpointLoopSummerizer. */
		LOOP_SUMMARIZER_FIXPOINT_ITERATIONS(KeyType.COUNTER),

		CALL_SUMMARIZER_APPLICATIONS(KeyType.COUNTER),

		CALL_SUMMARIZER_CACHE_MISSES(KeyType.COUNTER),
		/**
		 * Time spent to obtain call summaries, including the time to look search the cache and re-use existing
		 * summaries.
		 */
		CALL_SUMMARIZER_OVERALL_TIME(KeyType.TIMER),
		/** Time spent to compute completely new call summaries in case of cache misses. */
		CALL_SUMMARIZER_NEW_COMPUTATION_TIME(KeyType.TIMER),

		PROCEDURE_GRAPH_BUILDER_TIME(KeyType.TIMER),

		/** Time spent computing path expressions (= regexes) from graphs. */
		PATH_EXPR_TIME(KeyType.TIMER),

		/** Time spent converting regexes into dags. */
		REGEX_TO_DAG_TIME(KeyType.TIMER),

		/** Time spent compressing RegexDags. This can include multiple compression runs on different dags. */
		DAG_COMPRESSION_TIME(KeyType.TIMER),
		/** Sum of number of nodes in processed RegexDags before compression. */
		DAG_COMPRESSION_PROCESSED_NODES(KeyType.COUNTER),
		/** Sum of number of nodes in processed RegexDags after compression. */
		DAG_COMPRESSION_RETAINED_NODES(KeyType.COUNTER),;

		private final KeyType mType;

		Key(final KeyType type) {
			mType = type;
		}

		@Override
		public KeyType getType() {
			return mType;
		}

		@Override
		public String getName() {
			return name();
		}
	}

	private static class MaxTimerData {
		private long mTotalTime;
		private long mMaxTime;
	}
}
