package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * Interface for a expression visitor implemented
 * by an expression walker
 * 
 * @author GROSS-JAN
 *
 * @param <T>
 */
public interface IExpressionVisitor<T>
{
	void visitExpression(Expression expr);	
	void visitedExpression(Expression expr, T result);
	
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
}
