/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.BinaryExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorLogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.SingletonValueExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.test.mocks.ConsoleLogger;

/**
 * Helper functions for the interval test suite.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public final class HelperFunctions {

	private HelperFunctions() {
		// do not instantiate utility class
	}

	protected static IntervalDomainValue createInterval(final int lower, final int upper) {
		return new IntervalDomainValue(new IntervalValue(lower), new IntervalValue(upper));
	}

	protected static IntervalDomainValue createIntervalLeftUnbounded(final int upper) {
		return new IntervalDomainValue(new IntervalValue(), new IntervalValue(upper));
	}

	protected static IntervalDomainValue createIntervalRightUnbounded(final int lower) {
		return new IntervalDomainValue(new IntervalValue(lower), new IntervalValue());
	}

	protected static IntervalDomainValue createIntervalTop() {
		return new IntervalDomainValue();
	}

	protected static IntervalDomainValue createIntervalBottom() {
		return new IntervalDomainValue(true);
	}

	protected static BinaryExpressionEvaluator<IntervalDomainValue, IntervalDomainState> createBinaryEvaluator(
			final IntervalDomainValue first, final IntervalDomainValue second, final Operator operator,
			final EvaluatorType type, final int maxParallelStates, final int maxRecursionDepth) {

		final EvaluatorLogger logger = new EvaluatorLogger(new ConsoleLogger());
		final SingletonValueExpressionEvaluator<IntervalDomainValue, IntervalDomainState> value1Evaluator =
				new SingletonValueExpressionEvaluator<>(first, type, maxRecursionDepth, new IntervalValueFactory(),
						logger);
		final SingletonValueExpressionEvaluator<IntervalDomainValue, IntervalDomainState> value2Evaluator =
				new SingletonValueExpressionEvaluator<>(second, type, maxRecursionDepth, new IntervalValueFactory(),
						logger);
		final BinaryExpressionEvaluator<IntervalDomainValue, IntervalDomainState> binaryExpressionEvaluator =
				new BinaryExpressionEvaluator<>(logger, type, maxParallelStates, maxRecursionDepth,
						new IntervalValueFactory());

		binaryExpressionEvaluator.setOperator(operator);
		binaryExpressionEvaluator.addSubEvaluator(value1Evaluator);
		binaryExpressionEvaluator.addSubEvaluator(value2Evaluator);

		return binaryExpressionEvaluator;
	}

	private static String getMethodName() {
		final StackTraceElement[] ste = Thread.currentThread().getStackTrace();

		return ste[4].getMethodName();
	}

	protected static boolean computeResult(final IntervalDomainValue interval1, final IntervalDomainValue interval2,
			final IntervalDomainValue expectedResult, final IntervalDomainValue evaluatorResult) {

		System.out.println(getMethodName());
		System.out.println("Result  : " + evaluatorResult.toString());
		System.out.println("Expected: " + expectedResult.toString());
		System.out.println();

		if (interval1.isBottom() || interval2.isBottom()) {
			return evaluatorResult.isAbstractionEqual(expectedResult);
		}

		if (evaluatorResult.isBottom() && expectedResult.isBottom()) {
			return true;
		}

		if (evaluatorResult.isBottom() && !expectedResult.isBottom()) {
			return false;
		}

		final boolean lowerResult, upperResult;
		lowerResult = evaluatorResult.getLower().equals(expectedResult.getLower());
		upperResult = evaluatorResult.getUpper().equals(expectedResult.getUpper());
		return lowerResult && upperResult;
	}

	protected static boolean computeAdditionResult(final IntervalDomainValue interval1,
			final IntervalDomainValue interval2, final IntervalDomainValue expectedResult) {
		final Collection<IEvaluationResult<IntervalDomainValue>> result =
				createBinaryEvaluator(interval1, interval2, Operator.ARITHPLUS, EvaluatorType.INTEGER, 2, -1)
						.evaluate(new IntervalDomainState(new ConsoleLogger(), false), 0);
		boolean ret = true;
		for (final IEvaluationResult<IntervalDomainValue> res : result) {
			ret = ret && computeResult(interval1, interval2, expectedResult, res.getValue());
		}
		return ret;
	}

	protected static boolean computeSubtractionResult(final IntervalDomainValue interval1,
			final IntervalDomainValue interval2, final IntervalDomainValue expectedResult) {
		final Collection<IEvaluationResult<IntervalDomainValue>> result =
				createBinaryEvaluator(interval1, interval2, Operator.ARITHMINUS, EvaluatorType.INTEGER, 2, -1)
						.evaluate(new IntervalDomainState(new ConsoleLogger(), false), 0);
		boolean ret = true;
		for (final IEvaluationResult<IntervalDomainValue> res : result) {
			ret = ret && computeResult(interval1, interval2, expectedResult, res.getValue());
		}
		return ret;
	}

	protected static boolean computeMultiplicationResult(final IntervalDomainValue interval1,
			final IntervalDomainValue interval2, final IntervalDomainValue expectedResult) {
		final Collection<IEvaluationResult<IntervalDomainValue>> result =
				createBinaryEvaluator(interval1, interval2, Operator.ARITHMUL, EvaluatorType.INTEGER, 2, -1)
						.evaluate(new IntervalDomainState(new ConsoleLogger(), false), 0);
		boolean ret = true;
		for (final IEvaluationResult<IntervalDomainValue> res : result) {
			ret = ret && computeResult(interval1, interval2, expectedResult, res.getValue());
		}
		return ret;
	}

	protected static boolean computeIntersectionResult(final IntervalDomainValue interval1,
			final IntervalDomainValue interval2, final IntervalDomainValue expectedResult) {
		final IntervalDomainValue result = interval1.intersect(interval2);
		return computeResult(interval1, interval2, expectedResult, result);
	}

	protected static boolean computeMergedInterval(final IntervalDomainValue interval1,
			final IntervalDomainValue interval2, final IntervalDomainValue expected) {
		final IntervalDomainValue computed = interval1.merge(interval2);
		return computeResult(interval1, interval2, expected, computed);
	}

	protected static boolean checkInclusion(final IntervalDomainValue interval1, final IntervalDomainValue interval2) {
		return interval1.isContainedInBoth(interval2);
	}

	protected static boolean computeDivisionResultReal(final IntervalDomainValue interval1,
			final IntervalDomainValue interval2, final IntervalDomainValue expectedResult) {
		final Collection<IEvaluationResult<IntervalDomainValue>> result =
				createBinaryEvaluator(interval1, interval2, Operator.ARITHDIV, EvaluatorType.REAL, 2, -1)
						.evaluate(new IntervalDomainState(new ConsoleLogger(), false), 0);
		boolean ret = true;
		for (final IEvaluationResult<IntervalDomainValue> res : result) {
			ret = ret && computeResult(interval1, interval2, expectedResult, res.getValue());
		}
		return ret;
	}

	protected static boolean computeDivisionResultInteger(final IntervalDomainValue interval1,
			final IntervalDomainValue interval2, final IntervalDomainValue expectedResult) {
		final Collection<IEvaluationResult<IntervalDomainValue>> result =
				createBinaryEvaluator(interval1, interval2, Operator.ARITHDIV, EvaluatorType.INTEGER, 2, -1)
						.evaluate(new IntervalDomainState(new ConsoleLogger(), false), 0);
		boolean ret = true;
		for (final IEvaluationResult<IntervalDomainValue> res : result) {
			ret = ret && computeResult(interval1, interval2, expectedResult, res.getValue());
		}
		return ret;
	}
}
