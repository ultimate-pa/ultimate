package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * The ExpressionWalker gets an ExpressionVisitor 
 * 
 * @author GROSS-JAN
 *
 * @param <T>
 */
public class ExpressionWalker<T>
{
	private final IExpressionVisitor<T> mExpressionVisitor;
	
	public ExpressionWalker(IExpressionVisitor<T> visitor)
	{	
		mExpressionVisitor = visitor;
	}
	

	/**
	 * Apply the visitor an the given expression using
	 * the ExpressionWalker
	 * @param expr
	 */	
	public T walk(Expression expr)
	{
		mExpressionVisitor.visitExpression(expr);

		T result = null;
		
		// evaluate and store result in m_resultValue:
		if (expr instanceof ArrayAccessExpression)
		{
			result = mExpressionVisitor.visit((ArrayAccessExpression) expr);
		}
		else if (expr instanceof ArrayStoreExpression)
		{
			result = mExpressionVisitor.visit((ArrayStoreExpression) expr);
		}
		else if (expr instanceof BinaryExpression)
		{
			BinaryExpression binExpr = (BinaryExpression) expr;
			
			T left = walk(binExpr.getLeft());
			T right = walk(binExpr.getRight());
			
			result = mExpressionVisitor.visit(binExpr, left, right);
		}
		else if (expr instanceof BitvecLiteral)
		{
			result = mExpressionVisitor.visit((BitvecLiteral) expr);
		}
		else if (expr instanceof BitVectorAccessExpression)
		{			
			BitVectorAccessExpression bvExpr = (BitVectorAccessExpression) expr;
			T bvVal = walk(bvExpr.getBitvec());
			result = mExpressionVisitor.visit(bvExpr, bvVal, bvExpr.getStart(), bvExpr.getEnd());
		}
		else if (expr instanceof BooleanLiteral)
		{
			result = mExpressionVisitor.visit((BooleanLiteral) expr);
		}
		else if (expr instanceof IdentifierExpression)
		{
			result = mExpressionVisitor.visit((IdentifierExpression) expr);
		}
		else if (expr instanceof IntegerLiteral)
		{
			result = mExpressionVisitor.visit((IntegerLiteral) expr);
		}
		else if (expr instanceof RealLiteral)
		{
			result = mExpressionVisitor.visit((RealLiteral) expr);
		}
		else if (expr instanceof StringLiteral)
		{
			result = mExpressionVisitor.visit((StringLiteral) expr);
		}
		else if (expr instanceof UnaryExpression)
		{
			UnaryExpression unExpr = (UnaryExpression) expr;
			
			T value = walk(unExpr.getExpr());
			result = mExpressionVisitor.visit((UnaryExpression) expr, value);
		}
		else if (expr instanceof FunctionApplication)
		{
			FunctionApplication funcExpr = (FunctionApplication)expr;
						
			List<T> args = new ArrayList<T>();			
			for(Expression arg : funcExpr.getArguments())
			{
				args.add(walk(arg));
			}
			
			result = mExpressionVisitor.visit((FunctionApplication) expr, args);
		}
		else if (expr instanceof IfThenElseExpression)
		{
			IfThenElseExpression condExpr = (IfThenElseExpression) expr;
			
			T ifVlaue = walk(condExpr.getCondition());
			T thenValue = walk(condExpr.getThenPart());
			T elseValue = walk(condExpr.getElsePart());
			
			result = mExpressionVisitor.visit((IfThenElseExpression) expr, ifVlaue, thenValue, elseValue);
		}
		else
		{
			throw new UnsupportedOperationException("Extend the new type");
		}
		
		mExpressionVisitor.visitedExpression(expr, result);
		
		return result;
	}
}
