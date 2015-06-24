package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link SignDomainState} for the given Statement.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignDomainStatementProcessor<CodeBlock, BoogieVar> extends BoogieVisitor {

	private SignDomainState<CodeBlock, BoogieVar> mOldState;
	private SignDomainState<CodeBlock, BoogieVar> mNewState;

	Stack<IEvaluator<SignDomainValue, CodeBlock, BoogieVar>> stack;

	public SignDomainState<CodeBlock, BoogieVar> process(SignDomainState<CodeBlock, BoogieVar> oldState,
	        Statement statement) {
		mOldState = oldState;
		mNewState = (SignDomainState<CodeBlock, BoogieVar>) oldState.copy();

		// Process the current statement and alter mNewState
		processStatement(statement);

		return mNewState;
	}

	@Override
	protected void visit(AssignmentStatement statement) {

//		final LeftHandSide[] lhs = statement.getLhs();
//		final Expression[] rhs = statement.getRhs();
//
//		for (int i = 0; i < lhs.length; i++) {
//			assert mCurrentLhs == null;
//			processLeftHandSide(lhs[i]);
//			assert mCurrentLhs != null;
//			final String varname = mCurrentLhs;
//
//			assert mCurrentValue == null;
//			processExpression(rhs[i]);
//			assert mCurrentValue != null;
//			mNewState.setValue(varname, mCurrentValue);
//			mCurrentLhs = null;
//			mCurrentValue = null;
//		}
	}

	@Override
	protected void visit(BinaryExpression expr) {

		super.visit(expr);

		// TODO Generate Binary Evaluator
		
		// assert mCurrentValue == null;
		// processExpression(expr.getLeft());
		// assert mCurrentValue != null;
		// possiblyNegateCurrentValue();
		// final SignDomainValue left = mCurrentValue;
		// mCurrentValue = null;
		//
		// assert mCurrentValue == null;
		// processExpression(expr.getRight());
		// assert mCurrentValue != null;
		// possiblyNegateCurrentValue();
		// final SignDomainValue right = mCurrentValue;

		// mCurrentValue = SignMergeOperator.computeMergedValue(left, right);
	}

	@Override
	protected void visit(VariableLHS lhs) {
//		mCurrentLhs = lhs.getIdentifier();
		super.visit(lhs);
	}

	@Override
	protected void visit(RealLiteral expr) {
//		mCurrentValue = processRealLiteral(expr.getValue());
//		possiblyNegateCurrentValue();
	}

	@Override
	protected void visit(IntegerLiteral expr) {
//		mCurrentValue = processIntegerLiteral(expr.getValue());
//		possiblyNegateCurrentValue();
	}

	@Override
	protected void visit(UnaryExpression expr) {
		super.visit(expr);
	}
	
	private void addToStack(IEvaluator<SignDomainValue, CodeBlock, BoogieVar> evaluator) {
		
	}

}
