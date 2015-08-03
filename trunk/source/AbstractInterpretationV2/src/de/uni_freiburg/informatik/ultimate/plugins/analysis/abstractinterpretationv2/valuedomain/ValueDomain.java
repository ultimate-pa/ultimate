package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.valuedomain;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.ExpressionWalker;

public class ValueDomain implements IAbstractDomain<ValueState>
{
	private static final String s_domainID = "VALUES";

	private final Logger mLogger;

	private IAbstractMergeOperator<ValueState> mMergeOperator;
	private IAbstractWideningOperator<ValueState> mWideningOperator;

	private final IAbstractValueFactory<?> mIntValueFactory;
	private final IAbstractValueFactory<?> mRealValueFactory;
	private final IAbstractValueFactory<?> mBoolValueFactory;
	private final IAbstractValueFactory<?> mBitVectorValueFactory;
	private final IAbstractValueFactory<?> mStringValueFactory;

	private final ExpressionWalker<IAbstractValue<?>> mExpressionWalker;
	private final ExpressionVisitor mExpressionVisitor;

	public IAbstractValueFactory<?> getIntValueFactory()
	{
		return mIntValueFactory;
	}

	public IAbstractValueFactory<?> getRealValueFactory()
	{
		return mRealValueFactory;
	}

	public IAbstractValueFactory<?> getBoolValueFactory()
	{
		return mBoolValueFactory;
	}

	public IAbstractValueFactory<?> getBitVectorValueFactory()
	{
		return mBitVectorValueFactory;
	}

	public IAbstractValueFactory<?> getStringValueFactory()
	{
		return mStringValueFactory;
	}

	// private ValueState mCurrentState, mResultingState;

	private Map<Expression, IAbstractValue<?>> m_interimResults = new HashMap<Expression, IAbstractValue<?>>();

	/**
	 * Constructor
	 * 
	 * @param intValueFactory
	 * @param realValueFactory
	 * @param boolValueFactory
	 * @param bitVectorValueFactory
	 * @param stringValueFactory
	 */
	public ValueDomain(IAbstractValueFactory<?> intValueFactory,
			IAbstractValueFactory<?> realValueFactory,
			IAbstractValueFactory<?> boolValueFactory,
			IAbstractValueFactory<?> bitVectorValueFactory,
			IAbstractValueFactory<?> stringValueFactory,
			Logger logger)
	{
		mIntValueFactory = intValueFactory;
		mRealValueFactory = realValueFactory;
		mBoolValueFactory = boolValueFactory;
		mBitVectorValueFactory = bitVectorValueFactory;
		mStringValueFactory = stringValueFactory;
		mLogger = logger;
		
		mExpressionVisitor = new ExpressionVisitor(this, mLogger);
		mExpressionWalker = new ExpressionWalker<IAbstractValue<?>>(mExpressionVisitor);
	}

	// IAbstractDomain
	@Override
	public void setMergeOperator(IAbstractMergeOperator<ValueState> mergeOperator)
	{
		mMergeOperator = mergeOperator;
	}

	@Override
	public void setWideningOperator(IAbstractWideningOperator<ValueState> wideningOperator)
	{
		mWideningOperator = wideningOperator;
	}

	@Override
	public IAbstractMergeOperator<ValueState> getMergeOperator()
	{
		return mMergeOperator;
	}

	@Override
	public IAbstractWideningOperator<ValueState> getWideningOperator()
	{
		return mWideningOperator;
	}

	public static String getDomainID()
	{
		return s_domainID;
	}

	@Override
	public IAbstractState<ValueState> createState()
	{
		return new ValueState(this, false, false);
	}

	
	@Override
	public IAbstractState<ValueState> ApplyExpression(IAbstractState<ValueState> state, AbstractVariable target, IType targetType, Expression exp)
	{
		IAbstractValue<?> value = mExpressionWalker.walk(exp);

		if (value != null)
		{
			mLogger.debug(String.format("Assignment: %s := %s", target.getString(), value.toString()));

			((ValueState) state).writeValue(target, value);
		}
		return state;
	}

	@Override
	public IAbstractState<ValueState> ApplyHavoc(IAbstractState<ValueState> state, AbstractVariable target, IType targetType)
	{
		IAbstractValue<?> undef = getTopValueForType(targetType);
				
		if (undef != null)
		{
			mLogger.debug(String.format("Havocing: %s", target.getString()));
			((ValueState) state).writeValue(target, undef);
		}
		return state; 
	}

	@Override
	public IAbstractState<ValueState> ApplyAssume(IAbstractState<ValueState> state, Expression exp)
	{
		mExpressionVisitor.setState(state);
		IAbstractValue<?> formulaResult = mExpressionWalker.walk(exp);
		mLogger.debug(String.format("ASSUME \"%s\" => %s", exp, formulaResult.toString()));

		// reconstruct variable values that pass through the formula, adjust
		// resulting statement
		return applyAssumption(exp, state, formulaResult, false);
	}

	/**
	 * Applies the given expression as assumption. So the resulting state
	 * is the given state modified such that the given expression holds.
	 * 
	 * @param exp
	 * @param state
	 * @param formulaResult
	 * @param negate
	 * @return
	 */
	private IAbstractState<ValueState> applyAssumption(
			Expression exp, 
			IAbstractState<ValueState> state,
			IAbstractValue<?> formulaResult,
			boolean negate) 
	{			
		if (formulaResult == null) 
		{
			formulaResult = m_interimResults.get(exp);
		}
		
		if (formulaResult == null) 
		{
			mLogger.warn(String.format("Evaluating assume expression failed, returned null: %s", exp));
			return null;
		}

		// only apply when the assumption can be true
		if(state.isBottom() || formulaResult.isBottom() || formulaResult.isFalse()) 
		{
			// expression evaluates to false for all values, so there is no
			// resulting state.			
			return createBottom();
		}

		if (exp instanceof BinaryExpression) 
		{
			BinaryExpression binOp = (BinaryExpression) exp;
			BinaryExpression.Operator oper = binOp.getOperator();

			switch (oper) 
			{
				case LOGICAND:
				case LOGICOR:
					if (((oper == BinaryExpression.Operator.LOGICAND) && !negate)
							|| ((oper == BinaryExpression.Operator.LOGICOR) && negate)) 
					{						
						if (binOp.getLeft() instanceof BinaryExpression)
						{
							state = applyAssumption(binOp.getLeft(), state, null, negate);
						}
						if (binOp.getRight() instanceof BinaryExpression)
						{
						    state = applyAssumption(binOp.getRight(), state, null, negate);
						}
						return state;
					}
				case COMPLT:
				case COMPGT:
				case COMPLEQ:
				case COMPGEQ:
				case COMPEQ:
				case COMPNEQ:
				case LOGICIFF:
				case LOGICIMPLIES:					
					if (binOp.getLeft() instanceof IdentifierExpression) 
					{
						IdentifierExpression ieLeft = (IdentifierExpression) binOp.getLeft();
	
						return applyAssumptionResult(
								state, 
								new AbstractVariable(ieLeft.getIdentifier(), ieLeft.getDeclarationInformation()),
								formulaResult);
					}
	
					/*
					 * Not all comparison operators can simply be "mirrored" (e.g.
					 * [5,5] < [10,10] => [5,5], [10,10] > [5,5] => [10,10], so for
					 * some of them, we need to calculate the missing intermediate
					 * result
					 */
					if (binOp.getRight() instanceof IdentifierExpression) 
					{
						IdentifierExpression ieRight = (IdentifierExpression) binOp.getRight();
	
						IAbstractValue<?> leftValue = m_interimResults.get(binOp.getLeft());
						IAbstractValue<?> rightValue = m_interimResults.get(ieRight);
	
						IAbstractValue<?> rightHandAssumeResult;
						switch (binOp.getOperator()) 
						{
							case COMPLT:
								rightHandAssumeResult = negate ? rightValue.compareIsLess(leftValue) 
										: rightValue.compareIsGreaterEqual(leftValue);
								break;
								
							case COMPGT:
								rightHandAssumeResult = negate ? rightValue.compareIsGreater(leftValue)
										: rightValue.compareIsLessEqual(leftValue);
								break;
								
							case COMPLEQ:
								rightHandAssumeResult = negate ? rightValue.compareIsLessEqual(leftValue) 
										: rightValue.compareIsGreater(leftValue);
								break;
								
							case COMPGEQ:
								rightHandAssumeResult = negate ? rightValue.compareIsGreaterEqual(leftValue) 
										: rightValue.compareIsLess(leftValue);
								break;
								
							case COMPEQ:
							case COMPNEQ:
								rightHandAssumeResult = formulaResult;
								break;
								
							case LOGICAND:
							case LOGICIFF:
							case LOGICIMPLIES:
							case LOGICOR:
							default:
								// case not covered
								rightHandAssumeResult = null;
						}
						
						if (rightHandAssumeResult != null)
						{
							state = applyAssumptionResult(
									state,
									new AbstractVariable(ieRight.getIdentifier(), ieRight.getDeclarationInformation()), 
									rightHandAssumeResult);
						}
					}
					break;
				default:
					break;
			}

		}
		else if (exp instanceof UnaryExpression) 
		{
			UnaryExpression unaryExpression = (UnaryExpression) exp;
			if (unaryExpression.getOperator() == UnaryExpression.Operator.LOGICNEG)
			{
				return applyAssumption(unaryExpression.getExpr(), state, formulaResult, !negate);
			}
			else
			{
				throw new NotImplementedException();
			}
		}
		else if (exp instanceof BooleanLiteral) 
		{
			BooleanLiteral boolFormula = (BooleanLiteral)exp;
			if(boolFormula.getValue())
			{
				// "assume true;" -> nothing to narrow
				return state;
			}
			else
			{
				// "assume false;"
				return createBottom();
			}
		}	
		
		mLogger.warn(String.format("Could not reduce value range at assume statement \"%s\"", exp));
		
		return state;
	}
	
	/**
	 * TODO
	 * 
	 * @param identifier
	 * @param declarationInformation
	 * @param assumeResult
	 * @return
	 */
	private ValueState applyAssumptionResult(
			IAbstractState<ValueState> state,
			AbstractVariable variable, 			
			IAbstractValue<?> assumeResult) 
	{
		ValueState valueState = (ValueState) state; 
		IAbstractValue<?> oldValue = valueState.getValue(variable);
		
		if (oldValue != null)
		{
			IAbstractValue<?> newValue = oldValue.compareIsEqual(assumeResult);
			mLogger.debug(String.format("ASSUME for \"%s\": old[%s], assume[%s] => new[%s]", variable.getString(), oldValue, assumeResult, newValue));
			if (newValue != null) 
			{
				valueState.writeValue(variable, newValue);
				return valueState;
			}
		}
		return null;		
	}
	
	@Override
	public boolean ApplyAssert(IAbstractState<ValueState> state, Expression exp)
	{
		throw new NotImplementedException();
	}
	
	public IValueMergeOperator<?> mergeOperatorForDomainOfValue(IAbstractValue<?> trueResult)
	{
		throw new NotImplementedException();
	}

	private IAbstractValue<?> getTopValueForType(IType type)
	{
		if (type == null)
		{
			return null;
		}
		if (type instanceof PrimitiveType)
		{
			PrimitiveType pt = (PrimitiveType) type;
			IAbstractValue<?> topValue = null;
			if (pt.getTypeCode() == PrimitiveType.BOOL)
			{
				topValue = mBoolValueFactory.makeTopValue();
			}
			else if (pt.getTypeCode() == PrimitiveType.INT)
			{
				topValue = mIntValueFactory.makeTopValue();
			}
			else if (pt.getTypeCode() == PrimitiveType.REAL)
			{
				topValue = mRealValueFactory.makeTopValue();
			}
			else
			{
				mLogger.error(String.format("Unsupported primitive type \"%s\"", pt));
			}
			return topValue;
		}
		else
		{
			mLogger.error(String.format("Unsupported non-primitive type \"%s\" of %s", type, type.getClass()));
			return null;
		}
	}

	@Override
	public IAbstractState<ValueState> createBottom()
	{
		return new ValueState(this, true, false); 
	}

	@Override
	public IAbstractState<ValueState> createTop()
	{
		return new ValueState(this, false, true);
	}	
}