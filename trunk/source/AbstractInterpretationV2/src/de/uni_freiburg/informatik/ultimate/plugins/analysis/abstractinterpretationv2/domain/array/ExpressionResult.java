package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;

public class ExpressionResult<STATE extends IAbstractState<STATE>> {
	private final Expression mExpression;
	private final ArrayDomainState<STATE> mState;

	public ExpressionResult(final Expression expression, final ArrayDomainState<STATE> state) {
		mExpression = expression;
		mState = state;
	}

	public Expression getExpression() {
		return mExpression;
	}

	public ArrayDomainState<STATE> getState() {
		return mState;
	}
}
