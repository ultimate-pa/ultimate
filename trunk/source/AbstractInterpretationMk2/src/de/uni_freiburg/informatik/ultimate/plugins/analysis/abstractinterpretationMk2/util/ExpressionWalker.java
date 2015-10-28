package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * The ExpressionWalker gets an ExpressionVisitor and walks it through any given
 * expression. You can also override it to change the behavior at certain
 * expressions.
 * 
 * @author Jan Hättig
 *
 * @param <T>
 *            type of the result
 */
public class ExpressionWalker<T> {
	protected IExpressionVisitor<T> mExpressionVisitor;

	/**
	 * For overwriting ExpressionWalker<T> and IExpressionVisitor<T> and setting
	 * mExpressionVisitor to be 'this'
	 */
	protected ExpressionWalker() {
	}

	/**
	 * For using an ExpressionWalker<T> with a given ExpressionVisitor
	 * 
	 * @param visitor
	 */
	public ExpressionWalker(IExpressionVisitor<T> visitor) {
		mExpressionVisitor = visitor;
	}

	/**
	 * Apply the visitor an the given expression using the ExpressionWalker
	 * 
	 * @param expr
	 */
	public T walk(Expression expr) {
		mExpressionVisitor.visitExpression(expr);

		T result = null;

		// evaluate and store result in m_resultValue:
		if (expr instanceof ArrayAccessExpression) {
			result = mExpressionVisitor.visit((ArrayAccessExpression) expr);
		} else if (expr instanceof ArrayStoreExpression) {
			result = mExpressionVisitor.visit((ArrayStoreExpression) expr);
		} else if (expr instanceof BinaryExpression) {
			result = visit((BinaryExpression) expr);
		} else if (expr instanceof BitvecLiteral) {
			result = mExpressionVisitor.visit((BitvecLiteral) expr);
		} else if (expr instanceof BitVectorAccessExpression) {
			result = visit((BitVectorAccessExpression) expr);
		} else if (expr instanceof BooleanLiteral) {
			result = mExpressionVisitor.visit((BooleanLiteral) expr);
		} else if (expr instanceof IdentifierExpression) {
			result = mExpressionVisitor.visit((IdentifierExpression) expr);
		} else if (expr instanceof IntegerLiteral) {
			result = mExpressionVisitor.visit((IntegerLiteral) expr);
		} else if (expr instanceof RealLiteral) {
			result = mExpressionVisitor.visit((RealLiteral) expr);
		} else if (expr instanceof StringLiteral) {
			result = mExpressionVisitor.visit((StringLiteral) expr);
		} else if (expr instanceof UnaryExpression) {
			result = visit((UnaryExpression) expr);
		} else if (expr instanceof FunctionApplication) {
			result = visit((FunctionApplication) expr);
		} else if (expr instanceof IfThenElseExpression) {
			result = visit((IfThenElseExpression) expr);
		} else {
			throw new UnsupportedOperationException("Extend the new type");
		}

		mExpressionVisitor.visitedExpression(expr, result);

		return result;
	}

	/**
	 * Visiting a function applications. This can be overwritten to influence
	 * the visiting behavior.
	 * 
	 * @param funcExpr
	 * @return
	 */
	protected T visit(FunctionApplication funcExpr) {
		T result;
		List<T> args = new ArrayList<T>();
		for (Expression arg : funcExpr.getArguments()) {
			args.add(walk(arg));
		}

		result = mExpressionVisitor.visit(funcExpr, args);
		return result;
	}

	/**
	 * Visiting an if-then-else expression. This can be overwritten to influence
	 * the visiting behavior.
	 * 
	 * @param condExpr
	 * @return
	 */
	protected T visit(IfThenElseExpression condExpr) {
		T result;
		T ifVlaue = walk(condExpr.getCondition());
		T thenValue = walk(condExpr.getThenPart());
		T elseValue = walk(condExpr.getElsePart());

		result = mExpressionVisitor.visit(condExpr, ifVlaue, thenValue,
				elseValue);
		return result;
	}

	/**
	 * Visiting a unary expression This can be overwritten to influence the
	 * visiting behavior.
	 * 
	 * @param unExpr
	 * @return
	 */
	protected T visit(UnaryExpression unExpr) {
		T result = null;

		// if(mExpressionVisitor.prepareUnary(unExpr))
		// {
		T value = walk(unExpr.getExpr());
		result = mExpressionVisitor.visit(unExpr, value);
		// }
		return result;
	}

	/**
	 * Visiting a binary expression. This can be overwritten to influence the
	 * visiting behavior.
	 * 
	 * @param expr
	 * @return
	 */
	protected T visit(BinaryExpression expr) {
		T result = null;

		BinaryExpression binExpr = (BinaryExpression) expr;

		// if(mExpressionVisitor.prepareBinary(binExpr))
		// {
		T left = walk(binExpr.getLeft());
		T right = walk(binExpr.getRight());

		// result = mExpressionVisitor.visit(binExpr, left, right);
		// }
		return result;
	}

	/**
	 * Visiting a bit vector access expression. This can be overwritten to
	 * influence the visiting behavior.
	 * 
	 * @param bvExpr
	 * @return
	 */
	protected T visit(BitVectorAccessExpression bvExpr) {
		T result;
		T bvVal = walk(bvExpr.getBitvec());
		result = mExpressionVisitor.visit(bvExpr, bvVal, bvExpr.getStart(),
				bvExpr.getEnd());
		return result;
	}
}
