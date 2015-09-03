package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import static org.junit.Assert.*;

import java.math.BigDecimal;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;

public class IntervalDomainArithmeticTest {

	private IntervalDomainValue createInterval(int lower, int upper) {
		return new IntervalDomainValue(new IntervalValue(new BigDecimal(lower)), new IntervalValue(
		        new BigDecimal(upper)));
	}

	private IntervalBinaryExpressionEvaluator createBinaryEvaluator(IntervalDomainValue first,
	        IntervalDomainValue second, Operator operator) {
		IntervalSingletonValueExpressionEvaluator value1Evaluator = new IntervalSingletonValueExpressionEvaluator(first);
		IntervalSingletonValueExpressionEvaluator value2Evaluator = new IntervalSingletonValueExpressionEvaluator(
		        second);

		IntervalBinaryExpressionEvaluator binaryExpressionEvaluator = new IntervalBinaryExpressionEvaluator();

		binaryExpressionEvaluator.setOperator(operator);
		binaryExpressionEvaluator.addSubEvaluator(value1Evaluator);
		binaryExpressionEvaluator.addSubEvaluator(value2Evaluator);

		return binaryExpressionEvaluator;
	}

	private String getMethodName() {
		final StackTraceElement[] ste = Thread.currentThread().getStackTrace();

		return ste[3].getMethodName();
	}

	private boolean computeAdditionResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult) {

		final IEvaluationResult<IntervalDomainValue> result = createBinaryEvaluator(interval1, interval2,
		        Operator.ARITHPLUS).evaluate(null);

		System.out.println(getMethodName());
		System.out.println("Result  : " + result.toString());
		System.out.println("Expected: " + expectedResult.toString());
		System.out.println();

		final boolean lowerResult = result.getResult().getLower().getValue()
		        .equals(expectedResult.getLower().getValue());
		final boolean upperResult = result.getResult().getUpper().getValue()
		        .equals(expectedResult.getUpper().getValue());

		return lowerResult && upperResult;
	}

	@Test
	public void testIntervalAddition() {

		// Interval [1;10]
		IntervalDomainValue interval1 = createInterval(1, 10);

		// Interval [15;20]
		IntervalDomainValue interval2 = createInterval(15, 20);

		// Result should be [16;30]
		IntervalDomainValue expectedResult = createInterval(16, 30);

		assertTrue(computeAdditionResult(interval1, interval2, expectedResult));
	}

	@Test
	public void testNegativeIntervalAddition() {

		// Interval [-30;-20]
		IntervalDomainValue interval1 = createInterval(-30, -20);

		// Interval [-5;-1]
		IntervalDomainValue interval2 = createInterval(-5, -1);

		// Result should be [-35;-21]
		IntervalDomainValue expectedResult = createInterval(-35, -21);

		assertTrue(computeAdditionResult(interval1, interval2, expectedResult));
	}

	@Test
	public void testMixedNegativeIntervalAddition() {
		// Interval [-30; -20]
		IntervalDomainValue interval1 = createInterval(-30, -20);

		// Interval [5; 10]
		IntervalDomainValue interval2 = createInterval(5, 10);

		// Result should be [-25;-10]
		IntervalDomainValue expectedResult = createInterval(-25, -10);
		
		assertTrue(computeAdditionResult(interval1, interval2, expectedResult));
	}
}
