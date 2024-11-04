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

	private int mConditionalCommutativityIAIntegrations = 0;
	private int mConditionalCommutativityDFSRestarts = 0;
	private int mConditionalCommutativityConditionCalculations = 0;
	private int mConditionalCommutativityTraceChecks = 0;
	private int mConditionalCommutativityUnknownTraceChecks = 0;
	private int mConditionalCommutativityImperfectProofs = 0;
	private int mConditionalCommutativityCommutingCounterexamples = 0;
	private int mConditionalCommutativityQuantifiedConditions = 0;
	private int mConditionalCommutativityFalseConditions = 0;

	public void startStopwatch(final ConditionalCommutativityStopwatches stopwatch) {
		switch (stopwatch) {
		case CHECKER:
			start(ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityCheckTime);
			break;
		case CONDITION:
			start(ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityConditionCalculationTime);
			break;
		default:
			throw new AssertionError("unknown stopwatch");
		}
	}

	public void stopStopwatch(final ConditionalCommutativityStopwatches stopwatch) {
		switch (stopwatch) {
		case CHECKER:
			stop(ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityCheckTime);
			break;
		case CONDITION:
			stop(ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityConditionCalculationTime);
			break;
		default:
			throw new AssertionError("unknown stopwatch");
		}
	}

	public void addIAIntegration() {
		mConditionalCommutativityIAIntegrations++;
	}

	public void addDFSRestart() {
		mConditionalCommutativityDFSRestarts++;
	}

	public void addCommutingCounterexample() {
		mConditionalCommutativityCommutingCounterexamples++;
	}

	public void addConditionCalculation() {
		mConditionalCommutativityConditionCalculations++;
	}

	public void addTraceCheck() {
		mConditionalCommutativityTraceChecks++;
	}

	public void addUnknownTraceCheck() {
		mConditionalCommutativityUnknownTraceChecks++;
	}

	public void addImperfectProof() {
		mConditionalCommutativityImperfectProofs++;
	}

	public void addQuantifiedCondition() {
		mConditionalCommutativityQuantifiedConditions++;

	}

	public void addFalseCondition() {
		mConditionalCommutativityFalseConditions++;

	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return TYPE;
	}

	@Override
	public String[] getStopwatches() {
		return new String[] {
				ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityCheckTime.toString(),
				ConditionalCommutativityStatisticsDefinitions.ConditionalCommutativityConditionCalculationTime
						.toString() };
	}

	@Override
	public Object getValue(final String key) {
		final ConditionalCommutativityStatisticsDefinitions keyEnum =
				Enum.valueOf(ConditionalCommutativityStatisticsDefinitions.class, key);
		switch (keyEnum) {
		case ConditionalCommutativityCheckTime:
		case ConditionalCommutativityConditionCalculationTime:
			try {
				return getElapsedTime(key);
			} catch (final StopwatchStillRunningException e) {
				throw new AssertionError("clock still running: " + key);
			}
		case ConditionalCommutativityIAIntegrations:
			return mConditionalCommutativityIAIntegrations;
		case ConditionalCommutativityDFSRestarts:
			return mConditionalCommutativityDFSRestarts;
		case ConditionalCommutativityCommutingCounterexamples:
			return mConditionalCommutativityCommutingCounterexamples;
		case ConditionalCommutativityConditionCalculations:
			return mConditionalCommutativityConditionCalculations;
		case ConditionalCommutativityTraceChecks:
			return mConditionalCommutativityTraceChecks;
		case ConditionalCommutativityUnknownTraceChecks:
			return mConditionalCommutativityUnknownTraceChecks;
		case ConditionalCommutativityImperfectProofs:
			return mConditionalCommutativityImperfectProofs;
		case ConditionalCommutativityQuantifiedConditions:
			return mConditionalCommutativityQuantifiedConditions;
		case ConditionalCommutativityFalseConditions:
			return mConditionalCommutativityFalseConditions;
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

		ConditionalCommutativityCheckTime(StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

		ConditionalCommutativityConditionCalculationTime(StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

		ConditionalCommutativityIAIntegrations(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		ConditionalCommutativityDFSRestarts(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		ConditionalCommutativityCommutingCounterexamples(StatisticsType.INTEGER_ADDITION,
				StatisticsType.KEY_BEFORE_DATA),

		ConditionalCommutativityConditionCalculations(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		ConditionalCommutativityTraceChecks(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		ConditionalCommutativityUnknownTraceChecks(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		ConditionalCommutativityImperfectProofs(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		ConditionalCommutativityQuantifiedConditions(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		ConditionalCommutativityFalseConditions(StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA);

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
