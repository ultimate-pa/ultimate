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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.independence;

import java.util.function.BinaryOperator;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;

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
	private T mIndependentConditional;
	private T mIndependentUnconditional;
	private T mDependentConditional;
	private T mDependentUnconditional;
	private T mUnknownConditional;
	private T mUnknownUnconditional;
	private final BinaryOperator<T> mAggregator;

	private IndependenceResultAggregator(final T initial, final BinaryOperator<T> aggregator) {
		mIndependentConditional = initial;
		mIndependentUnconditional = initial;
		mDependentConditional = initial;
		mDependentUnconditional = initial;
		mUnknownConditional = initial;
		mUnknownUnconditional = initial;
		mAggregator = aggregator;
	}

	protected void aggregate(final T data, final Dependence result, final boolean conditional) {
		switch (result) {
		case DEPENDENT:
			aggregateDependent(data, conditional);
			return;
		case INDEPENDENT:
			aggregateIndependent(data, conditional);
			return;
		case UNKNOWN:
			aggregateUnknown(data, conditional);
			return;
		}
		throw new IllegalArgumentException("Unknown value: " + result);
	}

	protected void aggregateIndependent(final T data, final boolean conditional) {
		if (conditional) {
			mIndependentConditional = mAggregator.apply(mIndependentConditional, data);
		} else {
			mIndependentUnconditional = mAggregator.apply(mIndependentUnconditional, data);
		}
	}

	protected void aggregateDependent(final T data, final boolean conditional) {
		if (conditional) {
			mDependentConditional = mAggregator.apply(mDependentConditional, data);
		} else {
			mDependentUnconditional = mAggregator.apply(mDependentUnconditional, data);
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
		mIndependentConditional = mAggregator.apply(mIndependentConditional, other.mIndependentConditional);
		mIndependentUnconditional = mAggregator.apply(mIndependentUnconditional, other.mIndependentUnconditional);
		mDependentConditional = mAggregator.apply(mDependentConditional, other.mDependentConditional);
		mDependentUnconditional = mAggregator.apply(mDependentUnconditional, other.mDependentUnconditional);
		mUnknownConditional = mAggregator.apply(mUnknownConditional, other.mUnknownConditional);
		mUnknownUnconditional = mAggregator.apply(mUnknownUnconditional, other.mUnknownUnconditional);
	}

	public T getTotal() {
		return mAggregator.apply(getConditional(), getUnconditional());
	}

	public T getConditional() {
		return mAggregator.apply(getIndependentConditional(),
				mAggregator.apply(getDependentConditional(), getUnknownConditional()));
	}

	public T getUnconditional() {
		return mAggregator.apply(getIndependentUnconditional(),
				mAggregator.apply(getDependentUnconditional(), getUnknownUnconditional()));
	}

	public T getIndependent() {
		return mAggregator.apply(getIndependentConditional(), getIndependentUnconditional());
	}

	public T getIndependentConditional() {
		return mIndependentConditional;
	}

	public T getIndependentUnconditional() {
		return mIndependentUnconditional;
	}

	public T getDependent() {
		return mAggregator.apply(getDependentConditional(), getDependentUnconditional());
	}

	public T getDependentConditional() {
		return mDependentConditional;
	}

	public T getDependentUnconditional() {
		return mDependentUnconditional;
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
		str.append(", independent: ");
		str.append(dataPrinter.apply(getIndependent()));
		str.append(", independent conditional: ");
		str.append(dataPrinter.apply(getIndependentConditional()));
		str.append(", independent unconditional: ");
		str.append(dataPrinter.apply(getIndependentUnconditional()));
		str.append(", dependent: ");
		str.append(dataPrinter.apply(getDependent()));
		str.append(", dependent conditional: ");
		str.append(dataPrinter.apply(getDependentConditional()));
		str.append(", dependent unconditional: ");
		str.append(dataPrinter.apply(getDependentUnconditional()));
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

		public void increment(final Dependence result, final boolean conditional) {
			aggregate(1, result, conditional);
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

		public void stop(final Dependence result, final boolean conditional) {
			assert mStartTime != 0L : "Timer was not running";
			final long elapsed = System.nanoTime() - mStartTime;
			aggregate(elapsed, result, conditional);
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
