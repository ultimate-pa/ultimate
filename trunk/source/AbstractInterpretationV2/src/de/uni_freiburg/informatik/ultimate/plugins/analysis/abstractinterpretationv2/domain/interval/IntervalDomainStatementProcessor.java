package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link IntervalDomainState} for the given statement.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalDomainStatementProcessor extends BoogieVisitor {

	private final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final IUltimateServiceProvider mServices;

	private IntervalDomainState<CodeBlock, BoogieVar> mOldState;
	private IntervalDomainState<CodeBlock, BoogieVar> mNewState;

	IEvaluatorFactory<IntervalDomainValue, CodeBlock, BoogieVar> mEvaluatorFactory;
	ExpressionEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> mExpressionEvaluator;

	private String mLhsVariable;

	protected IntervalDomainStatementProcessor(IUltimateServiceProvider services,
	        IntervalStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mStateConverter = stateConverter;
		mServices = services;
	}

	public IntervalDomainState<CodeBlock, BoogieVar> process(IntervalDomainState<CodeBlock, BoogieVar> oldState,
	        Statement statement) {

		assert oldState != null;
		assert statement != null;

		mOldState = oldState;
		mNewState = (IntervalDomainState<CodeBlock, BoogieVar>) mOldState.copy();

		processStatement(statement);

		return mNewState;
	}

	@Override
	protected void visit(AssignmentStatement statement) {

		mEvaluatorFactory = new IntervalEvaluatorFactory(mServices, mStateConverter);

		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();

		for (int i = 0; i < lhs.length; i++) {
			assert mLhsVariable == null;
			processLeftHandSide(lhs[i]);
			assert mLhsVariable != null;

			processExpression(rhs[i]);
		}
	}

	@Override
	protected void visit(VariableLHS lhs) {
		mLhsVariable = lhs.getIdentifier();
	}
}
