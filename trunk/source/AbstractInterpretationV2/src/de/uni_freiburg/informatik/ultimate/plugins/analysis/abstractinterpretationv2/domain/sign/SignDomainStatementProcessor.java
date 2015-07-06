package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link SignDomainState} for the given Statement.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignDomainStatementProcessor extends BoogieVisitor {

	private SignDomainState<CodeBlock, BoogieVar> mOldState;
	private SignDomainState<CodeBlock, BoogieVar> mNewState;

	IEvaluatorFactory<Values, CodeBlock, BoogieVar> mEvaluatorFactory;
	ExpressionEvaluator<Values, CodeBlock, BoogieVar> mExpressionEvaluator;
	SignStateConverter<CodeBlock, BoogieVar> mStateConverter;

	private String mLhsVariable;

	protected SignDomainStatementProcessor(SignStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mStateConverter = stateConverter;
	}

	protected SignDomainState<CodeBlock, BoogieVar> process(SignDomainState<CodeBlock, BoogieVar> oldState,
	        Statement statement) {
		mOldState = oldState;
		mNewState = (SignDomainState<CodeBlock, BoogieVar>) oldState.copy();

		mLhsVariable = null;

		// Process the current statement and alter mNewState
		processStatement(statement);

		return mNewState;
	}

	@Override
	protected void visit(HavocStatement statement) {

		mEvaluatorFactory = new SignEvaluatorFactory(mStateConverter);

		final VariableLHS[] vars = statement.getIdentifiers();
		for (final VariableLHS var : vars) {
			mNewState.setValue(var.getIdentifier(), new SignDomainValue(Values.TOP));
		}

		super.visit(statement);
	}

	@Override
	protected void visit(AssignmentStatement statement) {
		mEvaluatorFactory = new SignEvaluatorFactory(mStateConverter);

		mExpressionEvaluator = new ExpressionEvaluator<Values, CodeBlock, BoogieVar>();

		// super.visit(statement);

		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();

		for (int i = 0; i < lhs.length; i++) {
			assert mLhsVariable == null;
			processLeftHandSide(lhs[i]);
			assert mLhsVariable != null;
			final String varname = mLhsVariable;
			mLhsVariable = null;

			processExpression(rhs[i]);
			assert mExpressionEvaluator.isFinished();
			final IEvaluationResult<?> result = mExpressionEvaluator.getRootEvaluator().evaluate(mOldState);

			if (!result.getType().equals(Values.class)) {
				throw new UnsupportedOperationException(
				        "The type of the assignment left hand side evaluation result is not allowed.");
			}

			final SignDomainValue newValue = new SignDomainValue((Values) result.getResult());
			mNewState.setValue(varname, newValue);
		}
	}

	@Override
	protected void visit(AssumeStatement statement) {

		// We are in a situation where we need to evaluate a logical formula (and update the abstract state
		// accordingly). Therefore, we use the SignLogicalEvaluatorFactory to allow for all evaluators to also be able
		// to interpret the result logically and return a new abstract state which will then be intersected with the
		// current abstract state.
		mEvaluatorFactory = new SignLogicalEvaluatorFactory(mStateConverter);

		mExpressionEvaluator = new ExpressionEvaluator<Values, CodeBlock, BoogieVar>();

		Expression formula = statement.getFormula();

		if (formula instanceof BooleanLiteral) {
			BooleanLiteral binform = (BooleanLiteral) formula;
			if (!binform.getValue()) {
				mNewState.setToBottom();
			}
			return;
		}

		processExpression(formula);

		IEvaluationResult<?> result = mExpressionEvaluator.getRootEvaluator().evaluate(mOldState);

		if (result instanceof SignDomainValue) {
			IEvaluationResult<Values> castedResult = (IEvaluationResult<Values>) result;

			// If the result is false (i.e. NEGATIVE) and we don't have any variable updates, we set the new abstract
			// state to \bot, as we have found an infeasible statement.
			if (castedResult.getResult().equals(Values.NEGATIVE)
			        && mExpressionEvaluator.getRootEvaluator().getVarIdentifiers().size() == 0) {
				mNewState.setToBottom();
			} else {
				for (String var : mExpressionEvaluator.getRootEvaluator().getVarIdentifiers()) {
					// TODO: Update abstract state
				}
				// mNewState.intersect(other)
				throw new UnsupportedOperationException("Hurz");
			}
		}

	}

	@Override
	protected void visit(AssertStatement statement) {
		mEvaluatorFactory = new SignLogicalEvaluatorFactory(mStateConverter);
		// TODO Auto-generated method stub
		super.visit(statement);
	}

	@Override
	protected void visit(BinaryExpression expr) {
		INAryEvaluator<?, CodeBlock, BoogieVar> evaluator;

		evaluator = mEvaluatorFactory.createNAryExpressionEvaluator(2);

		evaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(BooleanLiteral expr) {
		if (!(mEvaluatorFactory instanceof SignLogicalEvaluatorFactory)) {
			throw new UnsupportedOperationException(
			        "Boolean literas are only allowed in a boolean context, i.e. when visiting logic formulas.");
		}

		final SignLogicalEvaluatorFactory logicalEvaluatorFactory = (SignLogicalEvaluatorFactory) mEvaluatorFactory;

		final String booleanValue = expr.getValue() ? "True" : "False";

		IEvaluator<Values, CodeBlock, BoogieVar> booleanExpressionEvaluator = logicalEvaluatorFactory
		        .createSingletonValueExpressionEvaluator(booleanValue, Boolean.class);

		mExpressionEvaluator.addEvaluator(booleanExpressionEvaluator);
	}

	@Override
	protected void visit(RealLiteral expr) {
		IEvaluator<Values, CodeBlock, BoogieVar> integerExpressionEvaluator = mEvaluatorFactory
		        .createSingletonValueExpressionEvaluator(expr.getValue(), BigDecimal.class);

		mExpressionEvaluator.addEvaluator(integerExpressionEvaluator);
	}

	@Override
	protected void visit(IntegerLiteral expr) {

		IEvaluator<Values, CodeBlock, BoogieVar> integerExpressionEvaluator = mEvaluatorFactory
		        .createSingletonValueExpressionEvaluator(expr.getValue(), BigInteger.class);

		mExpressionEvaluator.addEvaluator(integerExpressionEvaluator);
	}

	@Override
	protected void visit(UnaryExpression expr) {

		SignUnaryExpressionEvaluator unaryExpressionEvaluator = (SignUnaryExpressionEvaluator) mEvaluatorFactory
		        .createNAryExpressionEvaluator(1);

		unaryExpressionEvaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(unaryExpressionEvaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(IdentifierExpression expr) {

		final IEvaluator<Values, CodeBlock, BoogieVar> variableExpressionEvaluator = mEvaluatorFactory
		        .createSingletonVariableExpressionEvaluator(expr.getIdentifier());

		mExpressionEvaluator.addEvaluator(variableExpressionEvaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(VariableLHS lhs) {
		mLhsVariable = lhs.getIdentifier();
	}

}
