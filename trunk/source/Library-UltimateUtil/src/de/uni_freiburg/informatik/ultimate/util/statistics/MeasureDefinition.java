/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019-2021 University of Freiburg
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

import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;

import de.uni_freiburg.informatik.ultimate.util.statistics.measures.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.StringCounter;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

/**
 * Represents the type (data type + aggregation function + pretty printer) of measure.
 *
 * @author schaetzc@tf.uni-freiburg.de
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class MeasureDefinition {
	public static final MeasureDefinition INT_COUNTER = new MeasureDefinition(() -> 0, Aggregate::intAdd,
			PrettyPrint::keyColonData, Convert::identity, Test::alwaysReady, Test::intIsEmpty);

	public static final MeasureDefinition LONG_COUNTER = new MeasureDefinition(() -> 0L, Aggregate::longAdd,
			PrettyPrint::keyColonData, Convert::identity, Test::alwaysReady, Test::longIsEmpty);

	public static final MeasureDefinition DOUBLE_COUNTER = new MeasureDefinition(() -> 0.0, Aggregate::doubleAdd,
			PrettyPrint::keyColonData, Convert::identity, Test::alwaysReady, Test::doubleIsEmpty);

	public static final MeasureDefinition INT_MAX = new MeasureDefinition(() -> 0, Aggregate::intMax,
			PrettyPrint::keyColonData, Convert::identity, Test::alwaysReady, Test::intIsEmpty);

	public static final MeasureDefinition LONG_TIME = new MeasureDefinition(() -> 0L, Aggregate::longAdd,
			PrettyPrint.dataAsTime(PrettyPrint::keyColonData), Convert::identity, Test::alwaysReady, Test::longIsEmpty);

	public static final MeasureDefinition LONG_TIME_MAX = new MeasureDefinition(() -> 0L, Aggregate::longMax,
			PrettyPrint.dataAsTime(PrettyPrint::keyColonData), Convert::identity, Test::alwaysReady, Test::longIsEmpty);

	public static final MeasureDefinition TT_TIMER = new MeasureDefinition(TimeTracker::new, Aggregate::timeTrackerAdd,
			PrettyPrint.dataAsTime(PrettyPrint::keyColonData), Convert::timeTrackerNanos, Test::timeTrackerIsReady,
			Test::timeTrackerIsEmpty);

	public static final MeasureDefinition TT_MAX_TIMER = new MeasureDefinition(TimeTracker::new,
			Aggregate::timeTrackerMax, PrettyPrint.dataAsTime(PrettyPrint::keyColonData), Convert::timeTrackerNanos,
			Test::timeTrackerIsReady, Test::timeTrackerIsEmpty);

	public static final MeasureDefinition IN_CA_RE_COUNTER = new MeasureDefinition(InCaReCounter::new,
			Aggregate::inCaReAdd, PrettyPrint::keyColonData, Convert::identity, Test::alwaysReady, Test::inCaReIsEmpty);

	public static final MeasureDefinition STATISTICS_AGGREGATOR =
			new MeasureDefinition(StatisticsAggregator::new, Aggregate::statisticsAggregator, PrettyPrint::keyColonData,
					Convert::identity, Test::alwaysReady, Test::statisticsDataProviderIsEmpty);

	public static final MeasureDefinition STATISTICS_CONVERT_AGGREGATE =
			new MeasureDefinition(StatisticsAggregator::new, Aggregate::statisticsConvertAndAggregate,
					PrettyPrint::keyColonData, Convert::identity, Test::alwaysReady, a -> false);

	public static final MeasureDefinition BACKWARD_COVERING_INFORMATION = new MeasureDefinition(
			BackwardCoveringInformation::new,
			(a, b) -> new BackwardCoveringInformation((BackwardCoveringInformation) a, (BackwardCoveringInformation) b),
			PrettyPrint::dataSpaceKey, a -> ((BackwardCoveringInformation) a).isEmpty());

	public static final MeasureDefinition INT_MULTI_COUNTER =
			new MeasureDefinition(() -> new int[0], Aggregate::intArrayAddElementWise, PrettyPrint::keyColonData,
					Convert::identity, Test::alwaysReady, Test::intArrayIsEmpty);

	public static final MeasureDefinition STRING_COUNTER =
			new MeasureDefinition(StringCounter::new, StringCounter::aggregate, PrettyPrint::keyColonData,
					Convert::identity, Test::alwaysReady, StringCounter::isEmpty);

	public static final MeasureDefinition FLAG_AND = new MeasureDefinition(() -> null, Aggregate::flagAnd,
			PrettyPrint::keyColonData, Convert::identity, Test::alwaysReady, Test::flagIsEmpty);

	public static final MeasureDefinition INT_COUNTER_ZERO = new MeasureDefinition(() -> -1, Aggregate::intAdd,
			PrettyPrint::keyColonData, Convert::identity, Test::alwaysReady, a -> Test.intIsEmpty(a, -1));

	private final Supplier<Object> mCreate;
	private final BinaryOperator<Object> mAggregate;
	private final BiFunction<String, Object, String> mPrettyPrinter;
	private final Predicate<Object> mIsReady;
	private final Function<Object, Object> mConverter;

	private final Predicate<Object> mIsEmpty;

	public MeasureDefinition(final Supplier<Object> create, final BinaryOperator<Object> aggregate,
			final BiFunction<String, Object, String> prettyprinter, final UnaryOperator<Object> converter,
			final Predicate<Object> isReady, final Predicate<Object> isEmpty) {
		mCreate = create;
		mAggregate = aggregate;
		mPrettyPrinter = prettyprinter;
		mConverter = converter;
		mIsReady = isReady;
		mIsEmpty = isEmpty;
	}

	/**
	 * Create a description of a measure, i.e., how it can be created, combined, printed, checked for various
	 * conditions, etc.
	 * 
	 * The created measure is always ready and does not need a conversion before aggregation.
	 * 
	 * @param create
	 *            Create an empty instance.
	 * @param aggregate
	 *            Aggregate two instances.
	 * @param prettyprinter
	 *            Print an instance.
	 * @param isEmpty
	 *            Check if an instance is empty, i.e., does not contain information.
	 */
	public MeasureDefinition(final Supplier<Object> create, final BinaryOperator<Object> aggregate,
			final BiFunction<String, Object, String> prettyprinter, final Predicate<Object> isEmpty) {
		this(create, aggregate, prettyprinter, Convert::identity, Test::alwaysReady, isEmpty);
	}

	public final boolean isReady(final Object obj) {
		return mIsReady.test(obj);
	}

	public final Object createEmpty() {
		return mCreate.get();
	}

	public final Object aggregate(final Object lhs, final Object rhs) {
		return mAggregate.apply(lhs, rhs);
	}

	/**
	 * TODO Make pretty printing only consider data. Whether to print "key: data" or "data key" should be consistent for
	 * all statistics elements.
	 */
	public final String prettyPrint(final String keyName, final Object data) {
		return mPrettyPrinter.apply(keyName, data);
	}

	public final Object convert(final Object o) {
		return mConverter.apply(o);
	}

	public final boolean isEmpty(final Object o) {
		return mIsEmpty.test(o);
	}
}