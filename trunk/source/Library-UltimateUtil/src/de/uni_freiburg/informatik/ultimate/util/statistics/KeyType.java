/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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

/**
 * Represents the type (data type + aggregation function + pretty printer) of an {@link IStatisticsElement}.
 * <p>
 * TODO use this enum in {@link IStatisticsElement}. See description below
 * <p>
 * This enum saves us from repeatedly writing code duplicates like
 * {@code ENUM_ITEM(Integer.class, Aggregate::intAdd, PrettyPrint::dataSpaceKey)} for <i>every</i> item in enums
 * implementing {@link IStatisticsElement}. <br>
 * This enum should be used by {@link IStatisticsElement} instead of forcing each implementing class to overwrite
 * {@link IStatisticsElement#getDataType()}, {@link IStatisticsElement#aggregate(Object, Object)} and so on. The new
 * {@link IStatisticsElement} would only require one method {@code KeyType getType()}. The other methods could be
 * implemented as defaults if something like {@code myStatsElement.getType().aggregate()} isn't acceptable. <br>
 * To do so we have to go through all implementations of {@link IStatisticsElement} and replace their constructor
 * arguments with a constant from this enum: {@code ENUM_ITEM(Some.class, someAggregator, comePrettyPrinter)} becomes
 * {@code ENUM_ITEM(KeyType.SOMETHING)} and we add {@code SOMETHING(Some.class, someAggregator, comePrettyPrinter)} to
 * this enum (in most cases the item {@code KeyType.SOMETHING} should already exist).
 * <p>
 * TODO When doing the rewrite we should also use pretty printers only print data. See comment on
 * {@link #prettyPrint(String, Object)}
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public enum KeyType {
	COUNTER(Integer.class, Aggregate::intAdd, PrettyPrint::keyColonData),
	RATIO(Double.class, Aggregate::doubleAdd, PrettyPrint::keyColonData),
	TIMER(Long.class, Aggregate::longAdd, PrettyPrint.dataAsTime(PrettyPrint::keyColonData)),
	MAX_TIMER(Long.class, Aggregate::longMax, PrettyPrint.dataAsTime(PrettyPrint::keyColonData)),;

	private final Class<?> mDataType;
	private final BinaryOperator<Object> mAggregate;
	private final BiFunction<String, Object, String> mPrettyPrinter;

	KeyType(final Class<?> dataType, final BinaryOperator<Object> aggregate,
			final BiFunction<String, Object, String> prettyprinter) {
		mDataType = dataType;
		mAggregate = aggregate;
		mPrettyPrinter = prettyprinter;
	}

	public Class<?> getDataType() {
		return mDataType;
	}

	public Object aggregate(final Object lhs, final Object rhs) {
		return mAggregate.apply(lhs, rhs);
	}

	/**
	 * TODO Make pretty printing only consider data. Whether to print "key: data" or "data key" should be consistent for
	 * all statistics elements.
	 */
	public String prettyPrint(final String keyName, final Object data) {
		return mPrettyPrinter.apply(keyName, data);
	}
}