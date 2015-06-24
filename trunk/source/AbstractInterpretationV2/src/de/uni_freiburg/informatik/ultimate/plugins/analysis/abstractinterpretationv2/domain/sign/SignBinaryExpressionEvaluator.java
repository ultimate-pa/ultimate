package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class SignBinaryExpressionEvaluator implements IEvaluator<Values, CodeBlock, BoogieVar> {

	private IEvaluator<Values, CodeBlock, BoogieVar> mLeftSubEvaluator;
	private IEvaluator<Values, CodeBlock, BoogieVar> mRightSubEvaluator;
	private BinaryExpression.Operator mOperator;

	@Override
	public IEvaluationResult<Values> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {

		final IEvaluationResult<Values> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final IEvaluationResult<Values> secondResult = mRightSubEvaluator.evaluate(currentState);

		switch (mOperator) {
		case ARITHPLUS:
			return performAddition(firstResult, secondResult);
			// case ARITHMINUS:
			// break;
			// case ARITHMUL:
			// break;
			// case ARITHDIV:
			// break;
		default:
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		}
	}

	/**
	 * Adds two {@link SignDomainState}s. {@link SignDomainState}s can be (+), (-), (0), T, &perp;.<br />
	 * 
	 * Addition is done in the following way:<br />
	 * 
	 * <ol>
	 * <li>Same values:<br />
	 * <ul>
	 * <li>(+) + (+) = (+)</li>
	 * <li>(-) + (-) = (-)</li>
	 * <li>(0) + (0) = (0)</li>
	 * <li>T + T = T</li>
	 * <li>&perp; + &perp; = &perp;</li>
	 * </ul>
	 * </li>
	 * <li>Different values:<br />
	 * <ul>
	 * <li>(0) + (+) = (+)</li>
	 * <li>(0) + (-) = (-)</li>
	 * <li>(+) + (0) = (+)</li>
	 * <li>(-) + (0) = (-)</li>
	 * <li>(+) + (-) = T</li>
	 * <li>(-) + (+) = T</li>
	 * </ul>
	 * </li>
	 * <li>Special cases:<br />
	 * <ul>
	 * <li>&perp; + ... = &perp;</li>
	 * <li>... + &perp; = &perp;</li>
	 * <li>T + ... = T (if ... != &perp;)</li>
	 * <li>... + T = T (if ... != &perp;)</li>
	 * </ul>
	 * </li>
	 * </ol>
	 * 
	 * @param first
	 *            The first evaluation result to be added.
	 * @param second
	 *            The second evaluation result to be added.
	 * @return A new evaluation result corresponding to the result of the addition operation.
	 */
	private IEvaluationResult<Values> performAddition(IEvaluationResult<Values> first, IEvaluationResult<Values> second) {

		assert first != null;
		assert second != null;

		// ===== Same values =====
		if (first.getResult().equals(second.getResult())) {
			return new SignDomainValue(first.getResult());
		}
		// ===== End Same values =====

		// ===== Special cases =====
		// If first = \bot or second = \bot, return \bot.
		if (first.getResult().equals(Values.BOTTOM) || second.getResult().equals(Values.BOTTOM)) {
			return new SignDomainValue(Values.BOTTOM);
		}

		// If one of them is \top, return \top.
		if (first.getResult().equals(Values.TOP) || second.getResult().equals(Values.TOP)) {
			return new SignDomainValue(Values.TOP);
		}
		// ===== End Special cases =====

		// ===== Different values =====
		// If one of the values is 0, return the other value.
		if (first.getResult().equals(Values.ZERO)) {
			return new SignDomainValue(second.getResult());
		}
		if (second.getResult().equals(Values.ZERO)) {
			return new SignDomainValue(first.getResult());
		}

		// If both values are different, return \top.
		if (!first.getResult().equals(second.getResult())) {
			return new SignDomainValue(Values.TOP);
		}
		// ===== End Different values =====

		// We should have covered all cases. If not, throw exception.
		throw new UnsupportedOperationException(
		        "There is one case which has not been covered in the addition of SignedDomain values. first: "
		                + first.getResult().toString() + ", second: " + second.getResult().toString());
	}

	@Override
	public void addSubEvaluator(IEvaluator<Values, CodeBlock, BoogieVar> evaluator) {
		assert mLeftSubEvaluator == null || mRightSubEvaluator == null;

		if (mLeftSubEvaluator == null) {
			mLeftSubEvaluator = evaluator;
			return;
		}

		mRightSubEvaluator = evaluator;
		return;
	}

	@Override
	public boolean hasFreeOperands() {
		return (mLeftSubEvaluator == null || mRightSubEvaluator == null);
	}

}
