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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.math.BigDecimal;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.EvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class HelperFunctions {
	protected static IntervalDomainValue createInterval(int lower, int upper) {
		return new IntervalDomainValue(new IntervalValue(new BigDecimal(lower)),
		        new IntervalValue(new BigDecimal(upper)));
	}

	protected static IntervalDomainValue createInterval() {
		return new IntervalDomainValue();
	}

	protected static IntervalBinaryExpressionEvaluator createBinaryEvaluator(IntervalDomainValue first,
	        IntervalDomainValue second, Operator operator) {
		IntervalSingletonValueExpressionEvaluator value1Evaluator = new IntervalSingletonValueExpressionEvaluator(
		        first);
		IntervalSingletonValueExpressionEvaluator value2Evaluator = new IntervalSingletonValueExpressionEvaluator(
		        second);

		IntervalBinaryExpressionEvaluator binaryExpressionEvaluator = new IntervalBinaryExpressionEvaluator();

		binaryExpressionEvaluator.setOperator(operator);
		binaryExpressionEvaluator.addSubEvaluator(value1Evaluator);
		binaryExpressionEvaluator.addSubEvaluator(value2Evaluator);

		return binaryExpressionEvaluator;
	}

	private static String getMethodName() {
		final StackTraceElement[] ste = Thread.currentThread().getStackTrace();

		return ste[4].getMethodName();
	}

	protected static boolean computeResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult, IntervalDomainValue evaluatorResult) {

		System.out.println(getMethodName());
		System.out.println("Result  : " + evaluatorResult.toString());
		System.out.println("Expected: " + expectedResult.toString());
		System.out.println();

		if (interval1.isBottom() || interval2.isBottom()) {
			return evaluatorResult.equals(expectedResult);
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

	protected static boolean computeAdditionResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult) {

		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> result = createBinaryEvaluator(
		        interval1, interval2, Operator.ARITHPLUS).evaluate(null);

		return computeResult(interval1, interval2, expectedResult, result.getResult().getEvaluatedValue());
	}

	protected static boolean computeSubtractionResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult) {

		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> result = createBinaryEvaluator(
		        interval1, interval2, Operator.ARITHMINUS).evaluate(null);

		return computeResult(interval1, interval2, expectedResult, result.getResult().getEvaluatedValue());
	}

	protected static boolean computeMultiplicationResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult) {

		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> result = createBinaryEvaluator(
		        interval1, interval2, Operator.ARITHMUL).evaluate(null);

		return computeResult(interval1, interval2, expectedResult, result.getResult().getEvaluatedValue());
	}

	protected static boolean computeIntersectionResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult) {

		final IntervalDomainValue result = interval1.intersect(interval2);

		return computeResult(interval1, interval2, expectedResult, result);
	}
}
