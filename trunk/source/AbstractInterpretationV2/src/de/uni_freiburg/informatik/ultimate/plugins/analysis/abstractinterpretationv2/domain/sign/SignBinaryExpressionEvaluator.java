package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.util.HashSet;
import java.util.Set;

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
	private Set<String> mVariableSet;

	public SignBinaryExpressionEvaluator() {
		mVariableSet = new HashSet<String>();
	}

	/**
	 * Sets the operator of the binary expression.
	 * 
	 * @param operator
	 *            The operator to be set. Must be of {@link BinaryExpression#Operator}.
	 */
	protected void setOperator(BinaryExpression.Operator operator) {
		mOperator = operator;
	}

	@Override
	public IEvaluationResult<Values> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {

		for (String var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (String var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		
		final IEvaluationResult<Values> firstResult = mLeftSubEvaluator.evaluate(currentState);
		final IEvaluationResult<Values> secondResult = mRightSubEvaluator.evaluate(currentState);

		switch (mOperator) {
		// case LOGICIFF:
		// break;
		// case LOGICIMPLIES:
		// break;
		// case LOGICAND:
		// break;
		// case LOGICOR:
		// break;
		// case COMPLT:
		// break;
		// case COMPGT:
		// break;
		// case COMPLEQ:
		// break;
		// case COMPGEQ:
		// break;
		// case COMPEQ:
		// break;
		// case COMPNEQ:
		// break;
		// case COMPPO:
		// break;
		// case BITVECCONCAT:
		// break;
		// case ARITHMUL:
		// break;
		// case ARITHDIV:
		// break;
		// case ARITHMOD:
		// break;
		case ARITHPLUS:
			return performAddition(firstResult, secondResult);
		case ARITHMINUS:
			return performSubtraction(firstResult, secondResult);
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

	/**
	 * Subtracts two {@link SignDomainState}s. {@link SignDomainState}s can be (+), (-), (0), T, &perp;.<br />
	 * 
	 * Addition is done in the following way:<br />
	 * 
	 * <ol>
	 * <li>Same values:<br />
	 * <ul>
	 * <li>(+) - (+) = T</li>
	 * <li>(-) - (-) = T</li>
	 * <li>(0) - (0) = (0)</li>
	 * <li>T - T = T</li>
	 * <li>&perp; - &perp; = &perp;</li>
	 * </ul>
	 * </li>
	 * <li>Different values:<br />
	 * <ul>
	 * <li>(0) - (+) = (-)</li>
	 * <li>(0) - (-) = (+)</li>
	 * <li>(+) - (0) = (+)</li>
	 * <li>(-) - (0) = (-)</li>
	 * <li>(+) - (-) = (+)</li>
	 * <li>(-) - (+) = (-)</li>
	 * </ul>
	 * </li>
	 * <li>Special cases:<br />
	 * <ul>
	 * <li>&perp; - ... = &perp;</li>
	 * <li>... - &perp; = &perp;</li>
	 * <li>T - ... = T (if ... != &perp;)</li>
	 * <li>... - T = T (if ... != &perp;)</li>
	 * </ul>
	 * </li>
	 * </ol>
	 * 
	 * @param first
	 *            The first evaluation result to be subtracted.
	 * @param second
	 *            The second evaluation result to be subtracted.
	 * @return A new evaluation result corresponding to the result of the subtract operation.
	 */
	private IEvaluationResult<Values> performSubtraction(IEvaluationResult<Values> first,
	        IEvaluationResult<Values> second) {

		assert first != null;
		assert second != null;

		// ====== Same Values ======
		if (first.getResult().equals(Values.ZERO) && second.getResult().equals(Values.ZERO)) {
			return new SignDomainValue(Values.ZERO);
		}
		if (first.getResult().equals(Values.BOTTOM) || second.getResult().equals(Values.BOTTOM)) {
			return new SignDomainValue(Values.BOTTOM);
		}
		if (first.getResult().equals(second.getResult())) {
			return new SignDomainValue(Values.TOP);
		}
		// ====== End Same Values ======

		// ====== Different Values ======
		if (first.getResult().equals(Values.ZERO)) {
			return negateValue(first.getResult());
		}
		if (second.getResult().equals(Values.ZERO)) {
			return new SignDomainValue(first.getResult());
		}
		if (first.getResult().equals(Values.POSITIVE) && second.getResult().equals(Values.NEGATIVE)) {
			return new SignDomainValue(Values.POSITIVE);
		}
		if (first.getResult().equals(Values.NEGATIVE) && second.getResult().equals(Values.POSITIVE)) {
			return new SignDomainValue(Values.NEGATIVE);
		}
		// ====== End Different Values ======

		// We should have covered all cases. If not, throw exception.
		throw new UnsupportedOperationException(
		        "There is one case which has not been covered in the subtraction of SignedDomain values. first: "
		                + first.getResult().toString() + ", second: " + second.getResult().toString());
	}

	/**
	 * Adds a subevaluator to {@link this} if possible.
	 */
	@Override
	public void addSubEvaluator(IEvaluator<Values, CodeBlock, BoogieVar> evaluator) {
		if (mLeftSubEvaluator != null && mRightSubEvaluator != null) {
			throw new UnsupportedOperationException("There are no free sub evaluators left to be assigned.");
		}

		if (mLeftSubEvaluator == null) {
			mLeftSubEvaluator = evaluator;
			return;
		}

		mRightSubEvaluator = evaluator;
	}

	/**
	 * Returns true if {@link this} still has subevaluators that are not empty.
	 */
	@Override
	public boolean hasFreeOperands() {
		return (mLeftSubEvaluator == null || mRightSubEvaluator == null);
	}

	/**
	 * Negates the given value.
	 * 
	 * @param value
	 *            The value to negate.
	 * @return The negated value as new object.
	 */
	private SignDomainValue negateValue(Values value) {
		assert value != null;

		switch (value) {
		case POSITIVE:
			return new SignDomainValue(Values.NEGATIVE);
		case NEGATIVE:
			return new SignDomainValue(Values.POSITIVE);
		case TOP:
			return new SignDomainValue(Values.TOP);
		case BOTTOM:
			return new SignDomainValue(Values.BOTTOM);
		case ZERO:
			return new SignDomainValue(Values.ZERO);
		default:
			throw new UnsupportedOperationException("The sign domain value " + value.toString()
			        + " is not implemented.");
		}
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableSet;
	}
}
