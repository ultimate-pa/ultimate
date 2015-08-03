package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

import java.util.List;

import org.apache.log4j.Logger;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.ExpressionWalker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IExpressionVisitor;

public class ExpressionVisitor
implements IExpressionVisitor<IAbstractValue<?>>
{
	private final ValueDomain mDomain;
	private Logger mLogger;
	private ValueState mCurrentState;
	
	public ExpressionVisitor(ValueDomain domain, Logger logger)
	{
		mDomain = domain;
		mLogger = logger;
	}
	
	public void setState(IAbstractState<ValueState> currentState)
	{
		mCurrentState = (ValueState)currentState;
	}
	
	@Override
	public void visitExpression(Expression expr)
	{	
	}

	@Override
	public void visitedExpression(Expression expr, IAbstractValue<?> result)
	{	
		mLogger.debug("Expression result: " + result.toString());
	}

	@Override
	public IAbstractValue<?> visit(ArrayAccessExpression expr)
	{
		throw new NotImplementedException();
	}

	@Override
	public IAbstractValue<?> visit(ArrayStoreExpression expr)
	{
		throw new NotImplementedException();
	}

	@Override
	public IAbstractValue<?> visit(BinaryExpression expr, IAbstractValue<?> left, IAbstractValue<?> right)
	{
		switch(expr.getOperator())
		{
			case ARITHDIV:
				return left.divide(right);				
			case ARITHMINUS:
				return left.subtract(right);
			case ARITHMOD:
				return left.modulo(right);
			case ARITHMUL:
				return left.multiply(right);
			case ARITHPLUS:
				return left.add(right);
			case BITVECCONCAT:
				return left.bitVectorConcat(right);
			case COMPEQ:
				return left.compareIsEqual(right);
			case COMPGEQ:
				return left.compareIsGreaterEqual(right);
			case COMPGT:
				return left.compareIsGreater(right);
			case COMPLEQ:
				return left.compareIsLessEqual(right);
			case COMPLT:
				return left.compareIsLess(right);
			case COMPNEQ:
				return left.compareIsNotEqual(right);
			case COMPPO:
				throw new NotImplementedException();				
			case LOGICAND:
				return left.logicAnd(right);
			case LOGICIFF:
				return left.logicIff(right);
			case LOGICIMPLIES:
				return left.logicImplies(right);
			case LOGICOR:
				return left.logicOr(right);
			default:
				throw new NotImplementedException();			
		}		
	}

	@Override
	public IAbstractValue<?> visit(BitvecLiteral expr)
	{
		return mDomain.getBitVectorValueFactory().makeBitVectorValue(expr.getValue());
	}

	@Override
	public IAbstractValue<?> visit(BitVectorAccessExpression expr, IAbstractValue<?> bvVal, int start, int end)
	{
		return bvVal.bitVectorAccess(start,  end);
	}

	@Override
	public IAbstractValue<?> visit(BooleanLiteral expr)
	{
		return mDomain.getBoolValueFactory().makeBoolValue(expr.getValue());
	}
	
	@Override
	public IAbstractValue<?> visit(IntegerLiteral expr)
	{		
		return mDomain.getIntValueFactory().makeIntegerValue(expr.getValue());
	}

	@Override
	public IAbstractValue<?> visit(RealLiteral expr)
	{
		return mDomain.getRealValueFactory().makeRealValue(expr.getValue());
	}
	
	@Override
	public IAbstractValue<?> visit(StringLiteral expr)
	{
		return mDomain.getStringValueFactory().makeStringValue(expr.getValue());
	}

	@Override
	public IAbstractValue<?> visit(IdentifierExpression expr)
	{
		return mCurrentState.getValue(expr.getIdentifier());
	}

	@Override
	public IAbstractValue<?> visit(UnaryExpression expr, IAbstractValue<?> value)
	{
		// TODO: optimize double negation and not expression
		switch(expr.getOperator())
		{
			case ARITHNEGATIVE:
				return value.negative(); 				
			case LOGICNEG:
				return value.logicNot();				
			case OLD:
				throw new NotImplementedException();
				
			default:
				throw new NotImplementedException();			
		}
	}
	
	@Override
	public IAbstractValue<?> visit(IfThenElseExpression expr, IAbstractValue<?> ifValue, IAbstractValue<?> thenValue, IAbstractValue<?> elseValue)
	{
		IAbstractValue<?> condition = booleanFromAbstractValue(ifValue);
		IAbstractValue<?> antiCondition = condition.logicNot(); // TODO: Can be more precise

		if (condition.isTrue())
		{
			return thenValue;
		}

		if (antiCondition.isTrue())
		{
			return elseValue;
		}
				
		// merge both values
		IValueMergeOperator<?> mergeOp = mDomain.mergeOperatorForDomainOfValue(thenValue);
		return mergeOp.apply(thenValue, elseValue);
	}

	

	@Override
	public IAbstractValue<?> visit(FunctionApplication expr, List<IAbstractValue<?>> args)	
	{
		throw new NotImplementedException();
	}
	

	/**
	 * @param value
	 *            An abstract value to get a boolean value for
	 * @return A value in the boolean domain representing the given value: <br>
	 *         If it already is a value in the boolean domain, a copy is
	 *         returned. <br>
	 *         Else, a boolean value of FALSE is returned iff the given value is
	 *         bottom.
	 */
	private IAbstractValue<?> booleanFromAbstractValue(IAbstractValue<?> value)
	{
		IAbstractValueFactory<?> boolFactory = mDomain.getBoolValueFactory();
		if (value == null)
		{
			//mLogger.warn("Encountered a boolean value of null, using UNKNOWN instead.");
			return boolFactory.makeTopValue();
		}

		if (boolFactory.valueBelongsToDomainSystem(value))
		{
			return value.isBottom() ? boolFactory.makeBoolValue(false) : value;			
		}

		// TODO: do something specific if it is an Integer or a BitVector
		
		return boolFactory.makeBoolValue(!value.isBottom());
	}
}
