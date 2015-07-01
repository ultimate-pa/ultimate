package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Represents an expression corresponding to a single value in the {@link SignDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public abstract class SignSingletonValueExpressionEvaluator<T> implements IEvaluator<Values, CodeBlock, BoogieVar> {

	protected T mValue;

	public SignSingletonValueExpressionEvaluator(String value) {
		T number = instantiate(value);

		mValue = number;
	}

	@Override
	public final IEvaluationResult<Values> evaluate(IAbstractState<?, ?> currentState) {
		int num = getSignum();

		if (num > 0) {
			return new SignDomainValue(Values.POSITIVE);
		}

		if (num < 0) {
			return new SignDomainValue(Values.NEGATIVE);
		}

		return new SignDomainValue(Values.ZERO);
	}

	@Override
	public final void addSubEvaluator(IEvaluator<?, ?, ?> evaluator) {
		throw new UnsupportedOperationException("A sub evaluator cannot be added to a singleton expression type.");
	}

	@Override
	public final boolean hasFreeOperands() {
		return false;
	}

	protected abstract T instantiate(String value);
	protected abstract int getSignum();
}
