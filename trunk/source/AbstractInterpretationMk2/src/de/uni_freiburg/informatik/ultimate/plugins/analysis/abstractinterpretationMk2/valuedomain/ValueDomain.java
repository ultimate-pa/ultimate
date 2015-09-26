package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.*;

public class ValueDomain implements IAbstractDomain<ValueState> {
	private static final String s_domainID = "VALUES";

	private final Logger mLogger;

	private IAbstractMergeOperator<ValueState> mMergeOperator;
	private IAbstractWideningOperator<ValueState> mWideningOperator;

	private final IAbstractValueFactory<?> mIntValueFactory;
	private final IAbstractValueFactory<?> mRealValueFactory;
	private final IAbstractValueFactory<?> mBoolValueFactory;
	private final IAbstractValueFactory<?> mBitVectorValueFactory;
	private final IAbstractValueFactory<?> mStringValueFactory;

	private final ValueExpressionVisitor mExpressionVisitor;

	public IAbstractValueFactory<?> getIntValueFactory() {
		return mIntValueFactory;
	}

	public IAbstractValueFactory<?> getRealValueFactory() {
		return mRealValueFactory;
	}

	public IAbstractValueFactory<?> getBoolValueFactory() {
		return mBoolValueFactory;
	}

	public IAbstractValueFactory<?> getBitVectorValueFactory() {
		return mBitVectorValueFactory;
	}

	public IAbstractValueFactory<?> getStringValueFactory() {
		return mStringValueFactory;
	}

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
			IAbstractValueFactory<?> stringValueFactory, Logger logger) {
		mIntValueFactory = intValueFactory;
		mRealValueFactory = realValueFactory;
		mBoolValueFactory = boolValueFactory;
		mBitVectorValueFactory = bitVectorValueFactory;
		mStringValueFactory = stringValueFactory;
		mLogger = logger;

		mExpressionVisitor = new ValueExpressionVisitor(this, mLogger);
	}

	// IAbstractDomain
	@Override
	public void setMergeOperator(
			IAbstractMergeOperator<ValueState> mergeOperator) {
		mMergeOperator = mergeOperator;
	}

	@Override
	public void setWideningOperator(
			IAbstractWideningOperator<ValueState> wideningOperator) {
		mWideningOperator = wideningOperator;
	}

	@Override
	public IAbstractMergeOperator<ValueState> getMergeOperator() {
		return mMergeOperator;
	}

	@Override
	public IAbstractWideningOperator<ValueState> getWideningOperator() {
		return mWideningOperator;
	}

	public static String getDomainID() {
		return s_domainID;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractDomain#createState()
	 */
	@Override
	public IAbstractState<ValueState> createState() {
		return new ValueState(this, false);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#ApplyExpression(de
	 * .uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractState,
	 * de.uni_freiburg.informatik.ultimate.plugins
	 * .analysis.abstractinterpretationMk2.abstractdomain.TypedAbstractVariable,
	 * de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression)
	 */
	@Override
	public IAbstractState<ValueState> applyExpression(
			IAbstractState<ValueState> state, TypedAbstractVariable target,
			Expression exp) {
		mExpressionVisitor.prepare(state);
		IAbstractValue<?> value = null;

		if (exp instanceof ArrayStoreExpression) {
			ArrayStoreExpression ase = (ArrayStoreExpression) exp;
			IAbstractValue<?> oldValue = state.getConcrete().getValue(target);
			value = mExpressionVisitor.visit(ase.getValue());

			// merge with the old value, to only increase array states
			value = mergeOperatorForDomainOfValue(value).apply(oldValue, value);

			// TODO: do something better with arrays (using the indices)
		} else {
			value = mExpressionVisitor.visit(exp);
		}

		if (value == null) {
			value = mExpressionVisitor.visit(exp);
			throw new RuntimeException();
		}

		// write the result to the variable
		((ValueState) state).writeValue(target, value);

		// mLogger.debug(String.format("Assignment: %s := %s",
		// target.getString(), value.toString()));

		return state;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#ApplyHavoc(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractState, de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.TypedAbstractVariable)
	 */
	@Override
	public IAbstractState<ValueState> applyHavoc(
			IAbstractState<ValueState> state, TypedAbstractVariable target) {
		IAbstractValue<?> undef = getTopBottomValueForType(target.getType(),
				true);

		if (undef != null) {
			// mLogger.debug(String.format("Havocing: %s", target.getString()));
			((ValueState) state).writeValue(target, undef);
		}
		return state;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#ApplyAssume(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractState,
	 * de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression)
	 */
	@Override
	public List<IAbstractState<ValueState>> applyAssume(
			IAbstractState<ValueState> state, Expression exp) {
		mExpressionVisitor.prepare(state);
		IAbstractValue<?> formulaResult = mExpressionVisitor.visit(exp);

		String formulaResultStr = formulaResult == null ? "null"
				: formulaResult.toString();
		// mLogger.debug(String.format("ASSUME \"%s\" => %s", exp,
		// formulaResultStr));

		// only apply when the assumption can be true
		// null means it is some con-/disjunction and not bottom
		if (formulaResult == null
				|| !assumptionValueIsFalse(formulaResult, exp)) {
			// put the state in a list
			List<IAbstractState<ValueState>> states = new ArrayList<IAbstractState<ValueState>>();
			states.add(state);
			// reconstruct variable values that pass through the formula, adjust
			// resulting statement
			return applyAssumption(exp, states, formulaResult, false);
		}
		// bottom
		return new ArrayList<IAbstractState<ValueState>>();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#ApplyAssert(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractState,
	 * de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression)
	 */
	@Override
	public boolean checkAssert(IAbstractState<ValueState> state, Expression exp) {
		// TODO: this is not tested, since asserts are implemented as Assumes
		mLogger.warn("Untested code in ValueDomain.ApplyAssert(...)!");
		mExpressionVisitor.prepare(state);
		IAbstractValue<?> formulaResult = mExpressionVisitor.visit(exp);
		String formulaResultStr = formulaResult == null ? "null"
				: formulaResult.toString();
		// mLogger.debug(String.format("ASSERT \"%s\" => %s", exp,
		// formulaResultStr));
		return (!(formulaResult == null || !assumptionValueIsFalse(
				formulaResult, exp)));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#ApplyCall(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractState, de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractState, java.util.List,
	 * java.util.List)
	 */
	@Override
	public void applyExpressionScoped(IAbstractState<ValueState> newState,
			IAbstractState<ValueState> oldState,
			List<TypedAbstractVariable> targets, List<Expression> arguments) {
		mExpressionVisitor.prepare(oldState);

		ValueState vState = (ValueState) newState;
		// apply each expression one after the other
		for (int i = 0; i < targets.size(); i++) {
			TypedAbstractVariable target = targets.get(i);
			Expression argument = arguments.get(i);

			IAbstractValue<?> value = mExpressionVisitor.visit(argument);

			if (value == null) {
				throw new RuntimeException();
			}

			// mLogger.debug(String.format("Assignment: %s := %s",
			// target.getString(), value.toString()));
			vState.writeValue(target, value);
		}
	}

	/**
	 * Can be used by other classes
	 * 
	 * @return
	 */
	public Logger getLogger() {
		return mLogger;
	}

	/**
	 * Returns a string representing the ID of this domain
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		return s_domainID;
	}

	/** -------------- ---------------- -------------- **/
	/** -------------- Helper functions -------------- **/
	/** -------------- ---------------- -------------- **/

	/**
	 * Applies the given expression as assumption. So the resulting state is the
	 * given state modified such that the given expression holds.
	 * 
	 * @param exp
	 * @param state
	 * @param assumeResult
	 * @param negate
	 * @return
	 */
	private List<IAbstractState<ValueState>> applyAssumption(Expression exp,
			List<IAbstractState<ValueState>> states,
			IAbstractValue<?> assumeResult, boolean negate) {
		// get the actual result of the expression
		if (assumeResult == null) {
			assumeResult = mExpressionVisitor.getResult(exp, negate);
		}

		if (exp instanceof BinaryExpression) {
			BinaryExpression binOp = (BinaryExpression) exp;
			BinaryExpression.Operator oper = binOp.getOperator();

			switch (oper) {
			case LOGICIFF:
			case LOGICIMPLIES:
			case LOGICAND:
			case LOGICOR:

				// do each side if it is not a unary expression
				boolean applyLeft = binOp.getLeft() instanceof BinaryExpression;
				boolean applyRight = binOp.getRight() instanceof BinaryExpression;

				// AND: apply both sides
				// OR: apply on each side on a separate copy

				if (((oper == BinaryExpression.Operator.LOGICAND) && !negate)
						|| ((oper == BinaryExpression.Operator.LOGICOR) && negate)) {
					// a AND b
					// a NOR b = not(a) AND not(b)
					// do each side if it is not a unary expression
					if (applyLeft) {
						states = applyAssumption(binOp.getLeft(), states, null,
								negate);
					}
					if (applyRight) {
						states = applyAssumption(binOp.getRight(), states,
								null, negate);
					}
					return states;
				} else if ((oper == BinaryExpression.Operator.LOGICIMPLIES)
						&& negate) {
					// a NIMPL b = a AND not(b)
					if (applyLeft) {
						states = applyAssumption(binOp.getLeft(), states, null,
								false);
					}
					if (applyRight) {
						states = applyAssumption(binOp.getRight(), states,
								null, true);
					}
					return states;
				} else if (((oper == BinaryExpression.Operator.LOGICAND) && negate)
						|| ((oper == BinaryExpression.Operator.LOGICOR) && !negate)) {
					// a NAND b = not(a) OR not(b)
					// a OR b

					// here is where the number of resulting states doubles
					List<IAbstractState<ValueState>> newStates = new ArrayList<IAbstractState<ValueState>>();

					// do each side if it is not a unary expression
					// apply the assumption result for left and right on two
					// copies
					if (applyLeft) {
						newStates
								.addAll(applyAssumption(binOp.getLeft(),
										copyStatesIf(states, applyRight), null,
										negate));
					}
					if (applyRight) {
						newStates.addAll(applyAssumption(binOp.getRight(),
								states, null, negate));
					}
					return newStates;
				} else if ((oper == BinaryExpression.Operator.LOGICIMPLIES)
						&& !negate) {
					// a IMPL b = not(a) OR b
					// here is where the number of resulting states doubles
					List<IAbstractState<ValueState>> newStates = new ArrayList<IAbstractState<ValueState>>();

					if (applyLeft) {
						newStates.addAll(applyAssumption(binOp.getLeft(),
								copyStatesIf(states, applyRight), null, true));
					}
					if (applyRight) {
						newStates.addAll(applyAssumption(binOp.getRight(),
								states, null, false));
					}
					return newStates;
				} else if ((oper == BinaryExpression.Operator.LOGICIFF)) {
					// a IFF b = (a AND b) OR (not(a) AND not(b))
					// a NIFF b = (a AND not(b)) OR (not(a) AND b)

					// here is where the number of resulting states doubles
					List<IAbstractState<ValueState>> posStates = new ArrayList<IAbstractState<ValueState>>();
					List<IAbstractState<ValueState>> negStates = new ArrayList<IAbstractState<ValueState>>();

					// 'pos' (a AND b)
					posStates.addAll(applyAssumption(binOp.getLeft(),
							copyStatesIf(states, true), null, true));
					posStates = applyAssumption(binOp.getRight(), posStates,
							null, !negate);

					// 'neg' (not(a) AND not(b))
					states = applyAssumption(binOp.getLeft(), states, null,
							false);
					states = applyAssumption(binOp.getRight(), states, null,
							negate);

					states.addAll(posStates);

					// neg
					return states;
				}

			case COMPLT:
			case COMPGT:
			case COMPLEQ:
			case COMPGEQ:
			case COMPEQ:
			case COMPNEQ:
				boolean applied = false;
				if (binOp.getLeft() instanceof IdentifierExpression) {
					IdentifierExpression ieLeft = (IdentifierExpression) binOp
							.getLeft();

					states = applyAssumptionResult(
							states,
							new TypedAbstractVariable(ieLeft.getIdentifier(),
									ieLeft.getDeclarationInformation(), ieLeft
											.getType()), assumeResult);
					applied = true;
				}

				/*
				 * Not all comparison operators can simply be "mirrored" (e.g.
				 * [5,5] < [10,10] => [5,5], [10,10] > [5,5] => [10,10], so for
				 * some of them, we need to calculate the missing intermediate
				 * result
				 */
				if (binOp.getRight() instanceof IdentifierExpression) {
					IAbstractValue<?> leftValue = mExpressionVisitor.getResult(
							binOp.getLeft(), false);
					IAbstractValue<?> rightValue = mExpressionVisitor
							.getResult(binOp.getRight(), false);

					IAbstractValue<?> rightHandAssumeResult = null;
					switch (binOp.getOperator()) {
					case COMPLT:
						rightHandAssumeResult = negate ? rightValue
								.compareIsLessEqual(leftValue) : rightValue
								.compareIsGreater(leftValue);
						break;
					case COMPGT:
						rightHandAssumeResult = negate ? rightValue
								.compareIsGreaterEqual(leftValue) : rightValue
								.compareIsLess(leftValue);
						break;
					case COMPLEQ:
						rightHandAssumeResult = negate ? rightValue
								.compareIsLess(leftValue) : rightValue
								.compareIsGreaterEqual(leftValue);
						break;
					case COMPGEQ:
						rightHandAssumeResult = negate ? rightValue
								.compareIsGreater(leftValue) : rightValue
								.compareIsLessEqual(leftValue);
						break;

					case COMPEQ:
					case COMPNEQ:
						rightHandAssumeResult = assumeResult;
						break;

					default:
						throw new NotImplementedException();
					}

					if (rightHandAssumeResult != null) {
						IdentifierExpression ieRight = (IdentifierExpression) binOp
								.getRight();

						states = applyAssumptionResult(
								states,
								new TypedAbstractVariable(ieRight
										.getIdentifier(), ieRight
										.getDeclarationInformation(), ieRight
										.getType()), rightHandAssumeResult);
						applied = true;
					}
				}
				if (applied) {
					return states;
				}

			default:
				break;
			}

		} else if (exp instanceof UnaryExpression) {
			UnaryExpression unaryExpression = (UnaryExpression) exp;
			if (unaryExpression.getOperator() == UnaryExpression.Operator.LOGICNEG) {
				return applyAssumption(unaryExpression.getExpr(), states, null,
						!negate);
			} else {
				throw new NotImplementedException();
			}
		} else if (exp instanceof BooleanLiteral) {
			BooleanLiteral boolFormula = (BooleanLiteral) exp;
			if (boolFormula.getValue() != negate) {
				// "assume true;" or "assume !false;" -> nothing to narrow
				return states;
			} else {
				// "assume false;" or "assume !true";
				// return createBottom();
				throw new RuntimeException(
						"If the formula evaluates to false, applyAssumption must not be called");
			}
		}

		// mLogger.warn(String.format("Could not reduce value range at assume statement \"%s\"",
		// exp));
		return states;
	}

	/**
	 * Puts the assumption result into every state
	 * 
	 * @param states
	 * @param variable
	 * @param assumeResult
	 * @return
	 */
	private List<IAbstractState<ValueState>> applyAssumptionResult(
			List<IAbstractState<ValueState>> states,
			TypedAbstractVariable variable, IAbstractValue<?> assumeResult) {
		List<IAbstractState<ValueState>> result = new ArrayList<IAbstractState<ValueState>>();
		for (IAbstractState<ValueState> state : states) {
			IAbstractValue<?> oldValue = state.getConcrete().getValue(variable);

			if (oldValue == null) {
				continue;
			}
			// shrink the range to the variables original range
			IAbstractValue<?> newValue = oldValue.compareIsEqual(assumeResult);
			// mLogger.debug(String.format("ASSUME for \"%s\": old=[%s], assume=[%s] => new[%s]",
			// variable.getString(), oldValue, assumeResult, newValue));
			if (newValue != null && !newValue.isBottom()) {
				state.getConcrete().writeValue(variable, newValue);
				result.add(state);
			}
		}
		return result;
	}

	/**
	 * create a copy only if needed
	 *
	 * @param states
	 * @param copy
	 * @return
	 */
	protected List<IAbstractState<ValueState>> copyStatesIf(
			List<IAbstractState<ValueState>> states, boolean copy) {
		if (!copy) {
			return states;
		}

		List<IAbstractState<ValueState>> copyStates;
		copyStates = new ArrayList<IAbstractState<ValueState>>();
		for (IAbstractState<ValueState> state : states) {
			copyStates.add(state.copy());
		}
		return copyStates;
	}

	/**
	 * Creates a top or a bottom value for the given type
	 * 
	 * @param type
	 *            the type of which we want to have a top or bottom value
	 * @param top
	 *            true: create top, false: create bottom
	 * @return
	 */
	public IAbstractValue<?> getTopBottomValueForType(IType type, boolean top) {
		if (type == null) {
			throw new RuntimeException();
		}

		IAbstractValue<?> returnValue = null;

		if (type instanceof de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType) {
			type = ((de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType) type)
					.getValueType();
		}

		if (type instanceof PrimitiveType) {
			PrimitiveType pt = (PrimitiveType) type;
			if (pt.getTypeCode() == PrimitiveType.BOOL) {
				returnValue = top ? mBoolValueFactory.makeTopValue()
						: mBoolValueFactory.makeBottomValue();
			} else if (pt.getTypeCode() == PrimitiveType.INT) {
				returnValue = top ? mIntValueFactory.makeTopValue()
						: mIntValueFactory.makeBottomValue();
			} else if (pt.getTypeCode() == PrimitiveType.REAL) {
				returnValue = top ? mRealValueFactory.makeTopValue()
						: mRealValueFactory.makeBottomValue();
			} else {
				mLogger.error(String.format(
						"Unsupported primitive type \"%s\"", pt));
			}
			return returnValue;
		}

		// mLogger.error(String.format("Unsupported non-primitive type \"%s\" of %s",
		// type, type.getClass()));
		return null;
	}

	public IValueMergeOperator<?> mergeOperatorForDomainOfValue(
			IAbstractValue<?> value) {
		ValueMergeOperator mop = (ValueMergeOperator) mMergeOperator;

		if (mIntValueFactory.valueBelongsToDomainSystem(value)) {
			return (IValueMergeOperator<?>) mop.getIntOperator();
		} else if (mBoolValueFactory.valueBelongsToDomainSystem(value)) {
			return (IValueMergeOperator<?>) mop.getBoolOperator();
		} else if (mRealValueFactory.valueBelongsToDomainSystem(value)) {
			return (IValueMergeOperator<?>) mop.getRealOperator();
		} else if (mBitVectorValueFactory.valueBelongsToDomainSystem(value)) {
			return (IValueMergeOperator<?>) mop.getBitVectorOperator();
		} else if (mStringValueFactory.valueBelongsToDomainSystem(value)) {
			return (IValueMergeOperator<?>) mop.getStringOperator();
		} else {
			throw new RuntimeException();
		}
	}

	/**
	 * TODO
	 * 
	 * @param assumptionValue
	 * @param exp
	 * @return
	 */
	private boolean assumptionValueIsFalse(IAbstractValue<?> assumptionValue,
			Expression exp) {
		if (mBoolValueFactory.valueBelongsToDomainSystem(assumptionValue)) {
			return assumptionValue.isFalse();
		} else {
			return assumptionValue.isBottom();
		}
	}

}
