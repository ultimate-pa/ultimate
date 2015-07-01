package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class SignLogicalExpressionEvaluator implements
        INAryEvaluator<SignDomainState<CodeBlock, BoogieVar>, CodeBlock, BoogieVar> {

	private IEvaluator<?, ?, ?> mLeftSubEvaluator;
	private IEvaluator<?, ?, ?> mRightSubEvaluator;
	private BinaryExpression.Operator mOperator;
	private Set<String> mVariableSet;

	public SignLogicalExpressionEvaluator() {
		mVariableSet = new HashSet<String>();
	}

	@Override
	public void setOperator(BinaryExpression.Operator operator) {
		mOperator = operator;
	}

	@Override
	public IEvaluationResult<?> evaluate(
	        IAbstractState<?, ?> currentState) {

		for (String var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (String var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}

//		final IEvaluationResult<?> firstResult = mLeftSubEvaluator.evaluate(currentState);
//		final IEvaluationResult<?> secondResult = mRightSubEvaluator.evaluate(currentState);

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
		// case ARITHPLUS:
		// break;
		// case ARITHMINUS:
		// break;
		default:
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		}
	}

	@Override
	public void addSubEvaluator(IEvaluator<?, ?, ?> evaluator) {
		if (mLeftSubEvaluator != null && mRightSubEvaluator != null) {
			throw new UnsupportedOperationException("There are no free sub evaluators left to be assigned.");
		}

		if (mLeftSubEvaluator == null) {
			mLeftSubEvaluator = evaluator;
			return;
		}

		mRightSubEvaluator = evaluator;
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableSet;
	}

	@Override
	public boolean hasFreeOperands() {
		return (mLeftSubEvaluator == null || mRightSubEvaluator == null);
	}

	@Override
    public Class<SignDomainState<CodeBlock, BoogieVar>> getType() {
	    // TODO Auto-generated method stub
	    return null;
    }

}
