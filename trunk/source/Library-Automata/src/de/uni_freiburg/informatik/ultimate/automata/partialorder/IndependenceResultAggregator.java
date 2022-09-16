/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.function.BinaryOperator;
import java.util.function.Function;

/**
 * Collects data on independence query, separating between conditional and unconditional queries as well as based on the
 * result of the query.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <T>
 *            The type of data being collected
 */
public class IndependenceResultAggregator<T> {
	private T mPositiveConditional;
	private T mPositiveUnconditional;
	private T mNegativeConditional;
	private T mNegativeUnconditional;
	private T mUnknownConditional;
	private T mUnknownUnconditional;
	private final BinaryOperator<T> mAggregator;

	private IndependenceResultAggregator(final T initial, final BinaryOperator<T> aggregator) {
		mPositiveConditional = initial;
		mPositiveUnconditional = initial;
		mNegativeConditional = initial;
		mNegativeUnconditional = initial;
		mUnknownConditional = initial;
		mUnknownUnconditional = initial;
		mAggregator = aggregator;
	}

	protected void aggregate(final T data, final boolean result, final boolean conditional) {
		if (result) {
			aggregatePositive(data, conditional);
		} else {
			aggregateNegative(data, conditional);
		}
	}

	protected void aggregatePositive(final T data, final boolean conditional) {
		if (conditional) {
			mPositiveConditional = mAggregator.apply(mPositiveConditional, data);
		} else {
			mPositiveUnconditional = mAggregator.apply(mPositiveUnconditional, data);
		}
	}

	protected void aggregateNegative(final T data, final boolean conditional) {
		if (conditional) {
			mNegativeConditional = mAggregator.apply(mNegativeConditional, data);
		} else {
			mNegativeUnconditional = mAggregator.apply(mNegativeUnconditional, data);
		}
	}

	protected void aggregateUnknown(final T data, final boolean conditional) {
		if (conditional) {
			mUnknownConditional = mAggregator.apply(mUnknownConditional, data);
		} else {
			mUnknownUnconditional = mAggregator.apply(mUnknownUnconditional, data);
		}
	}

	protected void aggregate(final IndependenceResultAggregator<T> other) {
		mPositiveConditional = mAggregator.apply(mPositiveConditional, other.mPositiveConditional);
		mPositiveUnconditional = mAggregator.apply(mPositiveUnconditional, other.mPositiveUnconditional);
		mNegativeConditional = mAggregator.apply(mNegativeConditional, other.mNegativeConditional);
		mNegativeUnconditional = mAggregator.apply(mNegativeUnconditional, other.mNegativeUnconditional);
		mUnknownConditional = mAggregator.apply(mUnknownConditional, other.mUnknownConditional);
		mUnknownUnconditional = mAggregator.apply(mUnknownUnconditional, other.mUnknownUnconditional);
	}

	public T getTotal() {
		return mAggregator.apply(getConditional(), getUnconditional());
	}

	public T getConditional() {
		return mAggregator.apply(getPositiveConditional(),
				mAggregator.apply(getNegativeConditional(), getUnknownConditional()));
	}

	public T getUnconditional() {
		return mAggregator.apply(getPositiveUnconditional(),
				mAggregator.apply(getNegativeUnconditional(), getUnknownUnconditional()));
	}

	public T getPositive() {
		return mAggregator.apply(getPositiveConditional(), getPositiveUnconditional());
	}

	public T getPositiveConditional() {
		return mPositiveConditional;
	}

	public T getPositiveUnconditional() {
		return mPositiveUnconditional;
	}

	public T getNegative() {
		return mAggregator.apply(getNegativeConditional(), getNegativeUnconditional());
	}

	public T getNegativeConditional() {
		return mNegativeConditional;
	}

	public T getNegativeUnconditional() {
		return mNegativeUnconditional;
	}

	public T getUnknown() {
		return mAggregator.apply(getUnknownConditional(), getUnknownUnconditional());
	}

	public T getUnknownConditional() {
		return mUnknownConditional;
	}

	public T getUnknownUnconditional() {
		return mUnknownUnconditional;
	}

	/**
	 * Prints this instance.
	 *
	 * @param dataPrinter
	 *            A printing function for the data values.
	 * @return A string representing the instance
	 */
	public String print(final Function<T, String> dataPrinter) {
		final StringBuilder str = new StringBuilder();
		str.append("[ total: ");
		str.append(dataPrinter.apply(getTotal()));
		str.append(", positive: ");
		str.append(dataPrinter.apply(getPositive()));
		str.append(", positive conditional: ");
		str.append(dataPrinter.apply(getPositiveConditional()));
		str.append(", positive unconditional: ");
		str.append(dataPrinter.apply(getPositiveUnconditional()));
		str.append(", negative: ");
		str.append(dataPrinter.apply(getNegative()));
		str.append(", negative conditional: ");
		str.append(dataPrinter.apply(getNegativeConditional()));
		str.append(", negative unconditional: ");
		str.append(dataPrinter.apply(getNegativeUnconditional()));
		str.append(", unknown: ");
		str.append(dataPrinter.apply(getUnknown()));
		str.append(", unknown conditional: ");
		str.append(dataPrinter.apply(getUnknownConditional()));
		str.append(", unknown unconditional: ");
		str.append(dataPrinter.apply(getUnknownUnconditional()));
		str.append("] ");
		return str.toString();
	}

	/**
	 * A combination of counters for independence queries, separating between conditional and unconditional queries as
	 * well as based on the result.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 */
	public static class Counter extends IndependenceResultAggregator<Integer> {
		public Counter() {
			super(0, (x, y) -> x + y);
		}

		public void increment(final boolean result, final boolean conditional) {
			aggregate(1, result, conditional);
		}

		public void incrementUnknown(final boolean conditional) {
			aggregateUnknown(1, conditional);
		}

		public static Counter sum(final Counter lhs, final Counter rhs) {
			final Counter result = new Counter();
			result.aggregate(lhs);
			result.aggregate(rhs);
			return result;
		}
	}

	public static class Timer extends IndependenceResultAggregator<Long> {
		private long mStartTime;

		public Timer() {
			super(0L, (x, y) -> x + y);
		}

		public void start() {
			assert mStartTime == 0L : "Timer already running";
			mStartTime = System.nanoTime();
		}

		public void stop(final boolean result, final boolean conditional) {
			assert mStartTime != 0L : "Timer was not running";
			final long elapsed = System.nanoTime() - mStartTime;
			aggregate(elapsed, result, conditional);
			mStartTime = 0L;
		}

		public void stopUnknown(final boolean conditional) {
			assert mStartTime != 0L : "Timer was not running";
			final long elapsed = System.nanoTime() - mStartTime;
			aggregateUnknown(elapsed, conditional);
			mStartTime = 0L;
		}

		public static Timer sum(final Timer lhs, final Timer rhs) {
			final Timer result = new Timer();
			result.aggregate(lhs);
			result.aggregate(rhs);
			return result;
		}
	}
}
