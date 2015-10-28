package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.util.ExpressionVisitor;

public class ValueExpressionVisitor extends ExpressionVisitor<IAbstractValue<?>> {
	private final ValueDomain mDomain;
	private Logger mLogger;
	private ValueState mCurrentState;
	private Map<Expression, IAbstractValue<?>> mInterimResultsNormal;
	private Map<Expression, IAbstractValue<?>> mInterimResultsNegated;
	private boolean mNegate;

	/**
	 * Constructor.
	 * 
	 * @param domain
	 * @param logger
	 */
	public ValueExpressionVisitor(ValueDomain domain, Logger logger) {
		mNegate = false;
		mDomain = domain;
		mLogger = logger;
		mInterimResultsNormal = new HashMap<Expression, IAbstractValue<?>>();
		mInterimResultsNegated = new HashMap<Expression, IAbstractValue<?>>();
	}

	/**
	 * Prepares for evaluating an expression.
	 */
	public void prepare(IAbstractState<ValueState> currentState) {
		mCurrentState = (ValueState) currentState;
		mNegate = false;
		mInterimResultsNormal.clear();
		mInterimResultsNegated.clear();
	}

	/**
	 * Returns the sub result of the given expression
	 * 
	 * @param exp
	 * @return
	 */
	public IAbstractValue<?> getResult(Expression exp, boolean negated) {
		return negated ? mInterimResultsNegated.get(exp) : mInterimResultsNormal.get(exp);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.Expression)
	 */
	@Override
	public IAbstractValue<?> visit(Expression expr) {
		// mLogger.debug("Visiting expression: " + expr);

		boolean negated = mNegate;

		IAbstractValue<?> result = super.visit(expr);

		if (mNegate) {
			mLogger.warn("A negation was not consumed!");
		}

		if (negated) {
			mInterimResultsNegated.put(expr, result);
		} else {
			mInterimResultsNormal.put(expr, result);
		}
		// mLogger.debug("Expression (" + expr + ") result: " + result);

		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.ArrayAccessExpression)
	 */
	@Override
	public IAbstractValue<?> visit(ArrayAccessExpression expr) {
		// TODO: Do something better with the array

		Expression array = expr.getArray();
		if (array instanceof IdentifierExpression) {
			IdentifierExpression arrayIdent = (IdentifierExpression) array;
			IType type = ((ArrayType) arrayIdent.getType()).getValueType();
			TypedAbstractVariable abst = new TypedAbstractVariable(arrayIdent.getIdentifier(),
					arrayIdent.getDeclarationInformation(), type);
			if (!mCurrentState.hasVariable(abst)) {
				// mLogger.warn("Variable " + abst.toString() +
				// " was not found in state " + mCurrentState.toString());
				mCurrentState.declareVariable(abst);
			}

			return mCurrentState.getValue(abst);
		} else {
			return null;
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.ArrayStoreExpression)
	 */
	@Override
	public IAbstractValue<?> visit(ArrayStoreExpression expr) {
		throw new UnsupportedOperationException();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.BitvecLiteral)
	 */
	@Override
	public IAbstractValue<?> visit(BitvecLiteral expr) {
		return mDomain.getBitVectorValueFactory().makeBitVectorValue(expr.getValue());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visited(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.BitVectorAccessExpression, java.lang.Object,
	 * int, int)
	 */
	@Override
	public IAbstractValue<?> visited(BitVectorAccessExpression expr, IAbstractValue<?> bvVal, int start, int end) {
		return bvVal.bitVectorAccess(start, end);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.BooleanLiteral)
	 */
	@Override
	public IAbstractValue<?> visit(BooleanLiteral expr) {
		boolean val = expr.getValue();
		if (mNegate) {
			val = !val;
			mNegate = false;
		}
		return mDomain.getBoolValueFactory().makeBoolValue(val);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.IntegerLiteral)
	 */
	@Override
	public IAbstractValue<?> visit(IntegerLiteral expr) {
		return mDomain.getIntValueFactory().makeIntegerValue(expr.getValue());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.RealLiteral)
	 */
	@Override
	public IAbstractValue<?> visit(RealLiteral expr) {
		return mDomain.getRealValueFactory().makeRealValue(expr.getValue());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.StringLiteral)
	 */
	@Override
	public IAbstractValue<?> visit(StringLiteral expr) {
		return mDomain.getStringValueFactory().makeStringValue(expr.getValue());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.IdentifierExpression)
	 */
	@Override
	public IAbstractValue<?> visit(IdentifierExpression expr) {
		return mCurrentState.getValue(
				new TypedAbstractVariable(expr.getIdentifier(), expr.getDeclarationInformation(), expr.getType()));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.UnaryExpression)
	 */
	@Override
	public IAbstractValue<?> visit(UnaryExpression expr) {
		if (expr.getOperator() == Operator.LOGICNEG) {
			mNegate = !mNegate;
		}
		return super.visit(expr);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visited(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.UnaryExpression, java.lang.Object)
	 */
	@Override
	public IAbstractValue<?> visited(UnaryExpression expr, IAbstractValue<?> value) {
		switch (expr.getOperator()) {
		case ARITHNEGATIVE:
			return value == null ? null : value.negative();

		case LOGICNEG:
			if (mNegate) {
				mLogger.warn("A negation was not eaten!");
			}
			// the value must have been negated inside
			return mNegate ? value.logicNot() : value;

		case OLD:
		default:
			throw new UnsupportedOperationException();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visit(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.BinaryExpression)
	 */
	@Override
	public IAbstractValue<?> visit(BinaryExpression expr) {
		/*
		 * The negations are always brought "inside" and handled there
		 */
		switch (expr.getOperator()) {
		case LOGICAND:
			if (mNegate) {
				// NAND(a, b) == OR(not(a), not(b)
				mNegate = true;
				IAbstractValue<?> a = visit(expr.getLeft());
				mNegate = true;
				IAbstractValue<?> b = visit(expr.getRight());
				mNegate = false;

				if (resultIsBoolean(a)) {
					return a.logicOr(b);
				}

				// OR: one must be non-bottom
				if (isBottom(a) && isBottom(b)) {
					return mDomain.getTopBottomValueForType(expr.getType(), false);
				}
				// otherwise the value does not tell us anything
				// since the returned ranges of left and right
				// may be from different variables
				return null;
			} else {
				// AND(a, b)
				mNegate = false;
				IAbstractValue<?> a = visit(expr.getLeft());
				mNegate = false;
				IAbstractValue<?> b = visit(expr.getRight());
				mNegate = false;

				if (resultIsBoolean(a)) {
					return a.logicAnd(b);
				}
				// both must be non-bottom
				if (isBottom(a) || isBottom(b)) {
					return mDomain.getTopBottomValueForType(expr.getType(), false);
				}
				return null;
			}
		case LOGICIFF:
		// scope for a and b
		{
			// compute the negated results first
			// (so the non-negated will be remembered)
			mNegate = true;
			IAbstractValue<?> aNeg = visit(expr.getLeft());
			mNegate = true;
			IAbstractValue<?> bNeg = visit(expr.getRight());

			mNegate = false;
			IAbstractValue<?> a = visit(expr.getLeft());
			mNegate = false;
			IAbstractValue<?> b = visit(expr.getRight());
			mNegate = false;

			if (mNegate) {
				// NIFF(a, b) == NOR(AND(a, b), AND(not(a), not(b)))
				// == AND(NAND(a, b), NAND(not(a), not(b)))
				// == AND(OR(not(a), not(b)), OR(a, b))
				if (resultIsBoolean(a)) {
					IAbstractValue<?> pos = a.logicOr(b);
					IAbstractValue<?> neg = aNeg.logicOr(bNeg);
					return pos.logicAnd(neg);
				}

				// NIFF: one is bottom or the other
				if ((isBottom(a) && isBottom(b)) || (isBottom(aNeg) && isBottom(bNeg))) {
					return mDomain.getTopBottomValueForType(expr.getType(), false);
				}
				return null;
			} else {
				// IFF(a, b) == OR(AND(a, b), AND(not(a), not(b)))
				if (resultIsBoolean(a)) {
					IAbstractValue<?> pos = a.logicAnd(b);
					IAbstractValue<?> neg = aNeg.logicAnd(bNeg);
					return pos.logicOr(neg);
				}

				// IFF: one of the two NANDs must be satisfiable
				if ((isBottom(a) || isBottom(b)) && (isBottom(aNeg) || isBottom(bNeg))) {
					return mDomain.getTopBottomValueForType(expr.getType(), false);
				}
				return null;
			}
		}

		case LOGICIMPLIES:
			if (mNegate) {
				// NIMP(a, b) == NOR(not(a), b) == AND(a, not(b))
				mNegate = false;
				IAbstractValue<?> a = visit(expr.getLeft());
				mNegate = true;
				IAbstractValue<?> b = visit(expr.getRight());
				mNegate = false;

				if (resultIsBoolean(a)) {
					return a.logicAnd(b);
				}
				// AND: Both must be non-bottom
				if (isBottom(a) || isBottom(b)) {
					return mDomain.getTopBottomValueForType(expr.getType(), false);
				}
				return null;
			} else {
				// IMP(a, b) == OR(not(a), b)
				mNegate = true;
				IAbstractValue<?> a = visit(expr.getLeft());
				mNegate = false;
				IAbstractValue<?> b = visit(expr.getRight());
				mNegate = false;

				if (resultIsBoolean(a)) {
					return a.logicOr(b);
				}
				// OR: not both may be bottom
				if (isBottom(a) && isBottom(b)) {
					return mDomain.getTopBottomValueForType(expr.getType(), false);
				}
				return null;
			}

		case LOGICOR:
			// TODO: try to split it into two states
			if (mNegate) {
				// NOR(a, b) == AND(not(a), not(b))
				mNegate = true;
				IAbstractValue<?> a = visit(expr.getLeft());
				mNegate = true;
				IAbstractValue<?> b = visit(expr.getRight());
				mNegate = false;

				if (resultIsBoolean(a)) {
					return a.logicAnd(b);
				}
				// AND: Both must be non-bottom
				if (isBottom(a) || isBottom(b)) {
					return mDomain.getTopBottomValueForType(expr.getType(), false);
				}
				return null;
			} else {
				// OR(a, b)
				mNegate = false;
				IAbstractValue<?> a = visit(expr.getLeft());
				mNegate = false;
				IAbstractValue<?> b = visit(expr.getRight());
				mNegate = false;

				if (resultIsBoolean(a)) {
					return a.logicOr(b);
				}
				// OR: not both may be bottom
				if (isBottom(a) && isBottom(b)) {
					return mDomain.getTopBottomValueForType(expr.getType(), false);
				}
				return null;
			}

		default:
			boolean negate = mNegate;
			mNegate = false;
			IAbstractValue<?> left = visit(expr.getLeft());
			IAbstractValue<?> right = visit(expr.getRight());
			mNegate = negate;
			return visited(expr, left, right);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visited(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.BinaryExpression, java.lang.Object,
	 * java.lang.Object)
	 */
	@Override
	public IAbstractValue<?> visited(BinaryExpression expr, IAbstractValue<?> left, IAbstractValue<?> right) {
		switch (expr.getOperator()) {
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
			if (mNegate) {
				mNegate = false;
				return left.compareIsNotEqual(right);
			}
			return left.compareIsEqual(right);
		case COMPGEQ:
			if (mNegate) {
				mNegate = false;
				return left.compareIsLess(right);
			}
			return left.compareIsGreaterEqual(right);
		case COMPGT:
			if (mNegate) {
				mNegate = false;
				return left.compareIsLessEqual(right);
			}
			return left.compareIsGreater(right);
		case COMPLEQ:
			if (mNegate) {
				mNegate = false;
				return left.compareIsGreater(right);
			}
			return left.compareIsLessEqual(right);
		case COMPLT:
			if (mNegate) {
				mNegate = false;
				return left.compareIsGreaterEqual(right);
			}
			return left.compareIsLess(right);
		case COMPNEQ:
			if (mNegate) {
				mNegate = false;
				return left.compareIsEqual(right);
			}
			return left.compareIsNotEqual(right);

		case COMPPO:
		default:
			throw new UnsupportedOperationException();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .util.ExpressionVisitor#visited(de.uni_freiburg.informatik
	 * .ultimate.model.boogie.ast.IfThenElseExpression, java.lang.Object,
	 * java.lang.Object, java.lang.Object)
	 */
	@Override
	public IAbstractValue<?> visited(IfThenElseExpression expr, IAbstractValue<?> ifValue, IAbstractValue<?> thenValue,
			IAbstractValue<?> elseValue) {
		// TODO: the assume in the then and else is not applied here
		IAbstractValue<?> condition = booleanFromAbstractValue(ifValue);
		IAbstractValue<?> antiCondition = condition.logicNot(); // TODO: Can be
																// more precise

		if (condition.isTrue()) {
			return thenValue;
		}

		if (antiCondition.isTrue()) {
			return elseValue;
		}

		// merge both values
		IValueMergeOperator<?> mergeOp = mDomain.mergeOperatorForDomainOfValue(thenValue);

		return mergeOp.apply(thenValue, elseValue);
	}

	@Override
	public IAbstractValue<?> visited(FunctionApplication expr, List<IAbstractValue<?>> args) {
		throw new UnsupportedOperationException("This domain does not support function applications: " + expr);
	}

	/*
	 * ------------ HELPER FUNCTIONS ------------
	 */

	/**
	 * @param value
	 *            An abstract value to get a boolean value for
	 * @return A value in the boolean domain representing the given value: <br>
	 *         If it already is a value in the boolean domain, a copy is
	 *         returned. <br>
	 *         Else, a boolean value of FALSE is returned iff the given value is
	 *         bottom.
	 */
	private IAbstractValue<?> booleanFromAbstractValue(IAbstractValue<?> value) {
		IAbstractValueFactory<?> boolFactory = mDomain.getBoolValueFactory();
		if (value == null) {
			throw new RuntimeException("Deprecated code");
			// mLogger.warn("Encountered a boolean value of null, using UNKNOWN
			// instead.");
			// return boolFactory.makeTopValue();
		}

		if (boolFactory.valueBelongsToDomainSystem(value)) {
			return value.isBottom() ? boolFactory.makeBoolValue(false) : value;
		}

		// TODO: do something specific if it is an Integer or a BitVector

		return boolFactory.makeBoolValue(!value.isBottom());
	}

	private boolean resultIsBoolean(IAbstractValue<?> value) {
		IAbstractValueFactory<?> boolFactory = mDomain.getBoolValueFactory();
		return boolFactory.valueBelongsToDomainSystem(value);
	}

	private boolean isBottom(IAbstractValue<?> value) {
		return value != null && value.isBottom();
	}
}
