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
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.util.statistics.Aggregate;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.PrettyPrint;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

/**
 * Statistics for Sifa.
 * <p>
 * Stopwatches in this class can be nested like parenthesis, that is stopwatch {@code s} can be used as in
 * {@code start(s); start(s); stop(s); stop(s);}. The measured time is the time between the first {@code start}
 * and its corresponding {@code stop}.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class SifaStats extends StatisticsGeneratorWithStopwatches implements IStatisticsDataProvider {

	private static final StatisticsType<Key> sType = new StatisticsType<>(Key.class);

	private final Map<Key, Integer> mStopwatchNestingLevels = new EnumMap<>(Key.class);
	private final Map<Key, Integer> mIntCounters = new EnumMap<>(Key.class);

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


	@Override
	public Object getValue(final String keyName) {
		return getValue(Key.valueOf(keyName));
	}

	public Object getValue(final Key keyId) {
		if (keyId.isStopwatch()) {
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
		return sType.getKeys();
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return sType;
	}

	@Override
	public String[] getStopwatches() {
		return Arrays.stream(Key.values())
				.filter(Key::isStopwatch)
				.map(Enum::name)
				.toArray(String[]::new);
	}

	public enum Key implements IStatisticsElement {
		// TODO use pre-defined objects instead of repeated triplets (class, aggregate, prettyPrint)

		OVERALL_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),

		/** Number of procedures entered (excluding CallReturnSummaries) during interpretation of the icfg. */
		ICFG_INTERPRETER_ENTERED_PROCEDURES(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),

		DAG_INTERPRETER_EARLY_EXIT_QUERIES(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		DAG_INTERPRETER_EARLY_EXITS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),

		TOOLS_POST_APPLICATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		TOOLS_POST_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		TOOLS_POST_CALL_APPLICATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		TOOLS_POST_CALL_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		TOOLS_POST_RETURN_APPLICATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		TOOLS_POST_RETURN_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		TOOLS_QUANTIFIERELIM_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),

		/** Overall time spent answering queries. */
		FLUID_QUERY_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		/** Number of queries to fluid. */
		FLUID_QUERIES(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		/** Number of queries to fluid answered with "yes, abstract the state". */
		FLUID_YES_ANSWERS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),

		DOMAIN_JOIN_APPLICATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		DOMAIN_JOIN_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		DOMAIN_ALPHA_APPLICATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		DOMAIN_ALPHA_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		DOMAIN_WIDEN_APPLICATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		DOMAIN_WIDEN_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		DOMAIN_ISSUBSETEQ_APPLICATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		DOMAIN_ISSUBSETEQ_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		DOMAIN_ISBOTTOM_APPLICATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		DOMAIN_ISBOTTOM_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),

		LOOP_SUMMARIZER_APPLICATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		LOOP_SUMMARIZER_CACHE_MISSES(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		/** Time spent to obtain loop summaries, including the time to look search the cache and re-use existing summaries. */
		LOOP_SUMMARIZER_OVERALL_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		/** Time spent to compute completely new loop summaries in case of cache misses. */
		LOOP_SUMMARIZER_NEW_COMPUTATION_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		/** Overall number of iterations. This statistic is specific to FixpointLoopSummerizer. */
		LOOP_SUMMARIZER_FIXPOINT_ITERATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),

		CALL_SUMMARIZER_APPLICATIONS(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		CALL_SUMMARIZER_CACHE_MISSES(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		/** Time spent to obtain call summaries, including the time to look search the cache and re-use existing summaries. */
		CALL_SUMMARIZER_OVERALL_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		/** Time spent to compute completely new call summaries in case of cache misses. */
		CALL_SUMMARIZER_NEW_COMPUTATION_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),

		PROCEDURE_GRAPH_BUILDER_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),

		/** Time spent computing path expressions (= regexes) from graphs. */
		PATH_EXPR_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),

		/** Time spent converting regexes into dags. */
		REGEX_TO_DAG_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),

		/** Time spent compressing RegexDags. This can include multiple compression runs on different dags. */
		DAG_COMPRESSION_TIME(Long.class, Aggregate::longAdd, PrettyPrint::timeFromNanosSpaceKey),
		/** Sum of number of nodes in processed RegexDags before compression. */
		DAG_COMPRESSION_PROCESSED_NODES(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		/** Sum of number of nodes in processed RegexDags after compression. */
		DAG_COMPRESSION_RETAINED_NODES(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey),
		;

		private final Class<?> mDataType;
		private final BiFunction<Object, Object, Object> mAggregate;
		private final BiFunction<String, Object, String> mPrettyprinter;

		Key(final Class<?> dataType,
				final BiFunction<Object, Object, Object> aggregate,
				final BiFunction<String, Object, String> prettyprinter) {
			mDataType = dataType;
			mAggregate = aggregate;
			mPrettyprinter = prettyprinter;
		}

		@Override
		public Class<?> getDataType() {
			return mDataType;
		}

		@Override
		public Object aggregate(final Object lhs, final Object rhs) {
			return mAggregate.apply(lhs, rhs);
		}

		@Override
		public String prettyprint(final Object data) {
			return mPrettyprinter.apply(name(), data);
		}

		public boolean isStopwatch() {
			return name().endsWith("_TIME");
		}

		public boolean isIntCounter() {
			return !isStopwatch();
		}
	}
}
