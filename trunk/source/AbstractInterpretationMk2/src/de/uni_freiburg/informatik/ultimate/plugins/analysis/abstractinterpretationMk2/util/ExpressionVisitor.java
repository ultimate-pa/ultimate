package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * Visits an expression. Is no real visitor pattern. Call visit(Expression) it
 * will call the correct instance of visit. Override the visit functions to
 * implement the logic. Or override the visited functions, which receive the
 * results of the sub expressions as arguments.
 * 
 * @author GROSS-JAN
 *
 * @param <T>
 *            return type of each visit function
 */
public abstract class ExpressionVisitor<T> {
	/**
	 * Constructor
	 */
	public ExpressionVisitor() {
	}

	/**
	 * Apply the visitor an the given expression using the ExpressionWalker
	 * 
	 * @param expr
	 */
	public T visit(Expression expr) {
		if (expr instanceof UnaryExpression) {
			return visit((UnaryExpression) expr);
		} else if (expr instanceof BinaryExpression) {
			return visit((BinaryExpression) expr);
		} else if (expr instanceof ArrayAccessExpression) {
			return visit((ArrayAccessExpression) expr);
		} else if (expr instanceof ArrayStoreExpression) {
			return visit((ArrayStoreExpression) expr);
		} else if (expr instanceof BitvecLiteral) {
			return visit((BitvecLiteral) expr);
		} else if (expr instanceof BitVectorAccessExpression) {
			return visit((BitVectorAccessExpression) expr);
		} else if (expr instanceof BooleanLiteral) {
			return visit((BooleanLiteral) expr);
		} else if (expr instanceof IdentifierExpression) {
			return visit((IdentifierExpression) expr);
		} else if (expr instanceof IntegerLiteral) {
			return visit((IntegerLiteral) expr);
		} else if (expr instanceof RealLiteral) {
			return visit((RealLiteral) expr);
		} else if (expr instanceof StringLiteral) {
			return visit((StringLiteral) expr);
		} else if (expr instanceof FunctionApplication) {
			return visit((FunctionApplication) expr);
		} else if (expr instanceof IfThenElseExpression) {
			return visit((IfThenElseExpression) expr);
		} else {
			throw new UnsupportedOperationException("Extend the new type");
		}
	}

	public T visit(BinaryExpression expr) {
		T left = visit(expr.getLeft());
		T right = visit(expr.getRight());

		return visited(expr, left, right);
	}

	public T visit(BitVectorAccessExpression expr) {
		BitVectorAccessExpression bvExpr = (BitVectorAccessExpression) expr;
		T bvVal = visit(bvExpr.getBitvec());
		return visited(bvExpr, bvVal, bvExpr.getStart(), bvExpr.getEnd());
	}

	public T visit(UnaryExpression expr) {
		T value = visit(expr.getExpr());
		return visited(expr, value);
	}

	public T visit(FunctionApplication expr) {
		List<T> args = new ArrayList<T>();
		for (Expression arg : expr.getArguments()) {
			args.add(visit(arg));
		}
		return visited(expr, args);
	}

	public T visit(IfThenElseExpression expr) {
		IfThenElseExpression condExpr = (IfThenElseExpression) expr;

		T ifVlaue = visit(condExpr.getCondition());
		T thenValue = visit(condExpr.getThenPart());
		T elseValue = visit(condExpr.getElsePart());

		return visited(condExpr, ifVlaue, thenValue, elseValue);
	}

	// ----- leafs -----
	public abstract T visit(ArrayAccessExpression expr);

	public abstract T visit(ArrayStoreExpression expr);

	public abstract T visit(BitvecLiteral expr);

	public abstract T visit(BooleanLiteral expr);

	public abstract T visit(IntegerLiteral expr);

	public abstract T visit(RealLiteral expr);

	public abstract T visit(StringLiteral expr);

	public abstract T visit(IdentifierExpression expr);

	public abstract T visited(FunctionApplication expr, List<T> args);

	public abstract T visited(UnaryExpression expr, T value);

	public abstract T visited(BinaryExpression expr, T left, T right);

	public abstract T visited(BitVectorAccessExpression expr, T val, int start,
			int end);

	public abstract T visited(IfThenElseExpression expr, T ifValue,
			T thenValue, T elseValue);
}
