package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class ExpressionResult<STATE extends IAbstractState<STATE>> {
	private final Expression mExpression;
	private final ArrayDomainState<STATE> mState;
	private final Set<IProgramVarOrConst> mAuxVars;

	public ExpressionResult(final Expression expression, final ArrayDomainState<STATE> state,
			final Set<IProgramVarOrConst> auxVars) {
		mExpression = expression;
		mState = state;
		mAuxVars = auxVars;
	}

	public Expression getExpression() {
		return mExpression;
	}

	public ArrayDomainState<STATE> getState() {
		return mState;
	}

	public Set<IProgramVarOrConst> getAuxVars() {
		return mAuxVars;
	}
}
