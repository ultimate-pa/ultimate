package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Expression evaluator for unary expressions in the interval domain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalUnaryExpressionEvaluator implements INAryEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> {

	private final static int BUFFER_MAX = 100;

	protected IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> mSubEvaluator;
	protected UnaryExpression.Operator mOperator;

	@Override
	public IEvaluationResult<IntervalDomainValue> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {

		IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> castedSubEvaluator = (IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar>) mSubEvaluator;

		final IEvaluationResult<IntervalDomainValue> subEvaluatorResult = (IEvaluationResult<IntervalDomainValue>) castedSubEvaluator;

		switch (mOperator) {
		case ARITHNEGATIVE:
			return negateValue(subEvaluatorResult.getResult());
		default:
			StringBuilder stringBuilder = new StringBuilder(BUFFER_MAX);
			stringBuilder.append("The operator ").append(mOperator).append(" is not implemented.");
			throw new UnsupportedOperationException(stringBuilder.toString());

		}
	}

	/**
	 * Negates the given interval.
	 * 
	 * @param interval
	 *            The interval to negate.
	 * @return A new interval which corresponds to the negated input interval.
	 */
	private IEvaluationResult<IntervalDomainValue> negateValue(IntervalDomainValue interval) {

		if (interval.isBottom()) {
			return new IntervalDomainValue(true);
		}

		if (interval.getLower().isInfinity() && interval.getUpper().isInfinity()) {
			return new IntervalDomainValue();
		}

		if (interval.getLower().isInfinity()) {
			return new IntervalDomainValue(new IntervalValue(interval.getUpper().getValue().negate()),
			        new IntervalValue());
		}

		if (interval.getUpper().isInfinity()) {
			return new IntervalDomainValue(new IntervalValue(), new IntervalValue(interval.getLower().getValue()
			        .negate()));
		}

		return new IntervalDomainValue(new IntervalValue(interval.getUpper().getValue().negate()), new IntervalValue(
		        interval.getLower().getValue().negate()));
	}

	@Override
	public void addSubEvaluator(IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> evaluator) {
		assert mSubEvaluator == null;
		assert evaluator != null;

		mSubEvaluator = evaluator;
	}

	@Override
	public Set<String> getVarIdentifiers() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean hasFreeOperands() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void setOperator(Object operator) {
		assert operator != null;
		assert operator instanceof Operator;
		mOperator = (Operator) operator;
	}

}
