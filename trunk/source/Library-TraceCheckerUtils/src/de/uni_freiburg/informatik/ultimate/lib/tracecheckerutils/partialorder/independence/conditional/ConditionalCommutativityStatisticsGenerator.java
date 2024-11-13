/*
 * Copyright (C) 2024 Marcel Ebbinghaus
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.conditional;

import java.util.Objects;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

/**
 * Generator for managing statistics regarding conditional commutativity checks.
 *
 * @author Marcel Ebbinghaus
 *
 */
public class ConditionalCommutativityStatisticsGenerator extends StatisticsGeneratorWithStopwatches
		implements IStatisticsDataProvider {

	public enum ConditionalCommutativityStopwatches {
		CHECKER, CONDITION
	}

	private static final StatisticsType<ConditionalCommutativityStatisticsDefinitions> TYPE =
			new StatisticsType<>(ConditionalCommutativityStatisticsDefinitions.class);

	private int mConditionCalculations = 0;
	private int mTraceChecks = 0;
	private int mUnknownTraceChecks = 0;
	private int mImperfectProofs = 0;
	private int mCommutingCounterexamples = 0;
	private int mQuantifiedConditions = 0;
	private int mFalseConditions = 0;

	public void startStopwatch(final ConditionalCommutativityStopwatches stopwatch) {
		switch (stopwatch) {
		case CHECKER:
			start(ConditionalCommutativityStatisticsDefinitions.CheckTime);
			break;
		case CONDITION:
			start(ConditionalCommutativityStatisticsDefinitions.ConditionCalculationTime);
			break;
		default:
			throw new AssertionError("unknown stopwatch");
		}
	}

	public void stopStopwatch(final ConditionalCommutativityStopwatches stopwatch) {
		switch (stopwatch) {
		case CHECKER:
			stop(ConditionalCommutativityStatisticsDefinitions.CheckTime);
			break;
		case CONDITION:
			stop(ConditionalCommutativityStatisticsDefinitions.ConditionCalculationTime);
			break;
		default:
			throw new AssertionError("unknown stopwatch");
		}
	}

	public void addCommutingCounterexample() {
		mCommutingCounterexamples++;
	}

	public void addConditionCalculation() {
		mConditionCalculations++;
	}

	public void addTraceCheck() {
		mTraceChecks++;
	}

	public void addUnknownTraceCheck() {
		mUnknownTraceChecks++;
	}

	public void addImperfectProof() {
		mImperfectProofs++;
	}

	public void addQuantifiedCondition() {
		mQuantifiedConditions++;

	}

	public void addFalseCondition() {
		mFalseConditions++;

	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return TYPE;
	}

	@Override
	public String[] getStopwatches() {
		return new String[] {
				ConditionalCommutativityStatisticsDefinitions.CheckTime.toString(),
				ConditionalCommutativityStatisticsDefinitions.ConditionCalculationTime
						.toString() };
	}

	@Override
	public Object getValue(final String key) {
		final ConditionalCommutativityStatisticsDefinitions keyEnum =
				Enum.valueOf(ConditionalCommutativityStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case CheckTime:
		case ConditionCalculationTime:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case CommutingCounterexamples:
			return mCommutingCounterexamples;
		case ConditionCalculations:
			return mConditionCalculations;
		case TraceChecks:
			return mTraceChecks;
		case UnknownTraceChecks:
			return mUnknownTraceChecks;
		case ImperfectProofs:
			return mImperfectProofs;
		case QuantifiedConditions:
			return mQuantifiedConditions;
		case FalseConditions:
			return mFalseConditions;
		default:
			throw new AssertionError("unknown data");
		}
	}

	/**
	 * Enum for statistics regarding conditional commutativity checks.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 */
	public enum ConditionalCommutativityStatisticsDefinitions implements IStatisticsElement {

		CheckTime(StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

		ConditionCalculationTime(StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

		CommutingCounterexamples(StatisticsType.INTEGER_ADDITION,
				StatisticsType.KEY_BEFORE_DATA),

		ConditionCalculations(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		TraceChecks(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		UnknownTraceChecks(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		ImperfectProofs(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		QuantifiedConditions(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		FalseConditions(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA);

		private final Function<Object, Function<Object, Object>> mAggr;
		private final Function<String, Function<Object, String>> mPrettyprinter;

		ConditionalCommutativityStatisticsDefinitions(final Function<Object, Function<Object, Object>> aggr,
				final Function<String, Function<Object, String>> prettyprinter) {
			mAggr = Objects.requireNonNull(aggr);
			mPrettyprinter = Objects.requireNonNull(prettyprinter);
		}

		@Override
		public Object aggregate(final Object o1, final Object o2) {
			return mAggr.apply(o1).apply(o2);
		}

		@Override
		public String prettyprint(final Object o) {
			return mPrettyprinter.apply(CoreUtil.getUpperToCamelCase(name())).apply(o);
		}
	}
}
