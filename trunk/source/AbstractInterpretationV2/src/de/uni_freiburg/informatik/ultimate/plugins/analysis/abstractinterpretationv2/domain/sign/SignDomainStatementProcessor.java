package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
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
	private String mCurrentLhs;

	protected SignDomainStatementProcessor(SignStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mEvaluatorFactory = new SignEvaluatorFactory(stateConverter);
	}

	protected SignDomainState<CodeBlock, BoogieVar> process(SignDomainState<CodeBlock, BoogieVar> oldState,
	        Statement statement) {
		mOldState = oldState;
		mNewState = (SignDomainState<CodeBlock, BoogieVar>) oldState.copy();

		// Process the current statement and alter mNewState
		processStatement(statement);

		return mNewState;
	}

	@Override
	protected void visit(HavocStatement statement) {

		final VariableLHS[] vars = statement.getIdentifiers();
		for (final VariableLHS var : vars) {
			mNewState.setValue(var.getIdentifier(), new SignDomainValue(Values.TOP));
		}

		super.visit(statement);
	}

	@Override
	protected void visit(AssignmentStatement statement) {
		mExpressionEvaluator = new ExpressionEvaluator<Values, CodeBlock, BoogieVar>();

		// super.visit(statement);

		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();
		mCurrentLhs = null;

		for (int i = 0; i < lhs.length; i++) {
			assert mCurrentLhs == null;
			processLeftHandSide(lhs[i]);
			assert mCurrentLhs != null;
			final String varname = mCurrentLhs;
			mCurrentLhs = null;

			processExpression(rhs[i]);
			assert mExpressionEvaluator.isFinished();
			final IEvaluationResult<Values> result = mExpressionEvaluator.getRootEvaluator().evaluate(mOldState);
			final SignDomainValue newValue = new SignDomainValue(result.getResult());
			mNewState.setValue(varname, newValue);
		}
	}

	@Override
    protected void visit(AssumeStatement statement) {
		
		mExpressionEvaluator = new ExpressionEvaluator<Values, CodeBlock, BoogieVar>();
		
		Expression formula = statement.getFormula();
		
		processExpression(formula);
		
		System.out.println("asdasd");
		
	    // TODO Auto-generated method stub
	    //super.visit(statement);
    }

	@Override
    protected void visit(AssertStatement statement) {
	    // TODO Auto-generated method stub
	    super.visit(statement);
    }

	@Override
	protected void visit(VariableLHS lhs) {
		mCurrentLhs = lhs.getIdentifier();
	}

	@Override
	protected void visit(BinaryExpression expr) {

		SignBinaryExpressionEvaluator binaryExpressionEvaluator = (SignBinaryExpressionEvaluator) mEvaluatorFactory
		        .createNAryExpressionEvaluator(2);

		binaryExpressionEvaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(binaryExpressionEvaluator);

		super.visit(expr);
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

}
