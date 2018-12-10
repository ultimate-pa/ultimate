package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.Evaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.NAryEvaluator;

/**
 * Evaluates Boogie {@link Expressions}s for a given {@link NonrelationalState}.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class NonrelationalEvaluator<STATE extends NonrelationalState<STATE, V>, V extends INonrelationalValue<V>>
		extends BoogieVisitor {
	private ExpressionEvaluator<V, STATE> mExpressionEvaluator;
	private final Map<Expression, ExpressionEvaluator<V, STATE>> mEvaluatorCache;
	private final IEvaluatorFactory<V, STATE> mEvaluatorFactory;
	private final BoogieSymbolTable mSymbolTable;
	private final IBoogieSymbolTableVariableProvider mBoogie2SmtSymbolTable;
	private boolean mOldScope;

	public NonrelationalEvaluator(final IEvaluatorFactory<V, STATE> evaluatorFactory,
			final BoogieSymbolTable boogieSymbolTable, final IBoogieSymbolTableVariableProvider bpl2SmtTable) {
		mEvaluatorFactory = evaluatorFactory;
		mEvaluatorCache = new HashMap<>();
		mSymbolTable = boogieSymbolTable;
		mBoogie2SmtSymbolTable = bpl2SmtTable;
	}

	public Collection<IEvaluationResult<V>> evaluate(final STATE state, final Expression expr) {
		mExpressionEvaluator = mEvaluatorCache.get(expr);
		if (mExpressionEvaluator == null) {
			mExpressionEvaluator = new ExpressionEvaluator<>();
			processExpression(expr);
			assert mExpressionEvaluator.isFinished() : "Expression evaluator is not finished";
			assert mExpressionEvaluator.getRootEvaluator() != null : "There is no root evaluator";
			mEvaluatorCache.put(expr, mExpressionEvaluator);
		}
		return getRootEvaluator().evaluate(state, 0);
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		if (expr instanceof ArrayStoreExpression || expr instanceof ArrayAccessExpression) {
			mExpressionEvaluator.addEvaluator(mEvaluatorFactory
					.createSingletonValueTopEvaluator(EvaluatorUtils.getEvaluatorType(expr.getType())));
			return expr;
		}
		if (expr instanceof UnaryExpression) {
			final UnaryExpression uexpr = (UnaryExpression) expr;
			if (uexpr.getOperator() == Operator.OLD) {
				mOldScope = true;
				final Expression rtr = super.processExpression(uexpr.getExpr());
				mOldScope = false;
				return rtr;
			}
		}
		return super.processExpression(expr);
	}

	public Evaluator<V, STATE> getRootEvaluator() {
		return mExpressionEvaluator.getRootEvaluator();
	}

	@Override
	protected void visit(final IntegerLiteral expr) {
		final Evaluator<V, STATE> evaluator =
				mEvaluatorFactory.createSingletonValueExpressionEvaluator(expr.getValue(), BigInteger.class);
		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(final RealLiteral expr) {
		final Evaluator<V, STATE> evaluator =
				mEvaluatorFactory.createSingletonValueExpressionEvaluator(expr.getValue(), BigDecimal.class);
		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(final BinaryExpression expr) {
		final NAryEvaluator<V, STATE> evaluator =
				mEvaluatorFactory.createNAryExpressionEvaluator(2, EvaluatorUtils.getEvaluatorType(expr.getType()));
		evaluator.setOperator(expr.getOperator());
		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(final FunctionApplication expr) {
		final Evaluator<V, STATE> evaluator;
		final List<Declaration> decls = mSymbolTable.getFunctionOrProcedureDeclaration(expr.getIdentifier());

		// If we don't have a specification for the function, we return top.
		if (decls == null || decls.isEmpty()) {
			evaluator =
					mEvaluatorFactory.createSingletonValueTopEvaluator(EvaluatorUtils.getEvaluatorType(expr.getType()));
		} else {

			assert decls.get(0) instanceof FunctionDeclaration;

			final FunctionDeclaration fun = (FunctionDeclaration) decls.get(0);

			// If the body is empty (as in undefined), we return top.
			if (fun.getBody() == null) {
				evaluator = mEvaluatorFactory.createFunctionEvaluator(fun.getIdentifier(), fun.getInParams().length,
						EvaluatorUtils.getEvaluatorType(expr.getType()));
			} else {
				// TODO Handle bitshifts, bitwise and, bitwise or, etc.
				throw new UnsupportedOperationException(
						"The function application for not inlined functions is not yet supported.");
			}
		}

		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(final IdentifierExpression expr) {
		final Evaluator<V, STATE> evaluator =
				mEvaluatorFactory.createSingletonVariableExpressionEvaluator(getBoogieVar(expr));
		mExpressionEvaluator.addEvaluator(evaluator);
		super.visit(expr);
	}

	@Override
	protected void visit(final UnaryExpression expr) {
		final NAryEvaluator<V, STATE> evaluator =
				mEvaluatorFactory.createNAryExpressionEvaluator(1, EvaluatorUtils.getEvaluatorType(expr.getType()));
		evaluator.setOperator(expr.getOperator());
		mExpressionEvaluator.addEvaluator(evaluator);
		super.visit(expr);
	}

	@Override
	protected void visit(final BooleanLiteral expr) {
		final Evaluator<V, STATE> evaluator = mEvaluatorFactory
				.createSingletonLogicalValueExpressionEvaluator(BooleanValue.getBooleanValue(expr.getValue()));
		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(final ArrayStoreExpression expr) {
		throw new UnsupportedOperationException("Proper array handling is not implemented.");
	}

	@Override
	protected void visit(final ArrayAccessExpression expr) {
		throw new UnsupportedOperationException("Proper array handling is not implemented.");
	}

	@Override
	protected void visit(final IfThenElseExpression expr) {
		final Evaluator<V, STATE> evaluator = mEvaluatorFactory.createConditionalEvaluator();
		mExpressionEvaluator.addEvaluator(evaluator);

		// Create a new expression for the negative case
		final UnaryExpression newUnary = new UnaryExpression(expr.getLocation(), expr.getCondition().getType(),
				UnaryExpression.Operator.LOGICNEG, expr.getCondition());

		// This expression should be added first to the evaluator inside the handling of processExpression.
		processExpression(newUnary);
	}

	private IProgramVarOrConst getBoogieVar(final IdentifierExpression expr) {
		IProgramVarOrConst returnVar =
				mBoogie2SmtSymbolTable.getBoogieVar(expr.getIdentifier(), expr.getDeclarationInformation(), false);

		if (returnVar != null) {
			if (mOldScope && returnVar instanceof IProgramNonOldVar) {
				return ((IProgramNonOldVar) returnVar).getOldVar();
			}
			return returnVar;
		}

		returnVar = mBoogie2SmtSymbolTable.getBoogieConst(expr.getIdentifier());
		assert returnVar != null;
		return returnVar;
	}

}
