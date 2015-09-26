package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * Interface for a expression visitor implemented by an expression walker
 * 
 * @author GROSS-JAN
 *
 * @param <T>
 */
public interface IExpressionVisitor<T> {
	/**
	 * This is called before any expression is visited
	 * 
	 * @param expr
	 *            the expression to be visited
	 */
	void visitExpression(Expression expr);

	/**
	 * This is called before any expression is visited
	 * 
	 * @param expr
	 */
	void visitedExpression(Expression expr, T result);

	/**
	 * Visit an array expression
	 * 
	 * @param expr
	 * @return
	 */
	T visit(ArrayAccessExpression expr);

	T visit(ArrayStoreExpression expr);

	T visit(BinaryExpression expr, T left, T right);

	T visit(BitvecLiteral expr);

	T visit(BitVectorAccessExpression expr, T val, int start, int end);

	T visit(BooleanLiteral expr);

	T visit(IntegerLiteral expr);

	T visit(RealLiteral expr);

	T visit(StringLiteral expr);

	T visit(IdentifierExpression expr);

	T visit(UnaryExpression expr, T value);

	T visit(FunctionApplication expr, List<T> args);

	T visit(IfThenElseExpression expr, T ifValue, T thenValue, T elseValue);

	// // TODO: remove these two
	// boolean prepareUnary(UnaryExpression expr);
	// boolean prepareBinary(BinaryExpression expr);
}
