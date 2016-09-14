package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Class to transform {@link Expression}s to an equivalent linear normal form (just used as container)
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public final class ExpressionTransformer {
	private BigInteger mConstant;
	private HashMap<String, BigInteger> mCoefficients;
	private final HashMap<String, IdentifierExpression> mIdentifiers;
	private boolean mIsLinear;
	private boolean mHasNormalForm;

	private ExpressionTransformer() {
		mConstant = BigInteger.ZERO;
		mCoefficients = new HashMap<>();
		mIdentifiers = new HashMap<>();
		mIsLinear = true;
		mHasNormalForm = false;
	}

	/**
	 * Tranforms a given {@link Expression} to an equivalent linear normal form (if possible), w.r.t logical operators
	 * Normal form: conjunctions / disjunctions of: k1 * x1 + ... + kn * xn op k0 (where xi are variables and ki
	 * constant integers)
	 */
	public static Expression transform(final Expression expr) {
		if (expr instanceof UnaryExpression) {
			return new ExpressionTransformer().transformUnary((UnaryExpression) expr);
		}
		if (expr instanceof BinaryExpression) {
			return new ExpressionTransformer().transformBinary((BinaryExpression) expr);
		}
		return expr;
	}

	/**
	 * Transforms a {@link UnaryExpression} to normal form Just moves the not inside and uses atomicTransform
	 */
	private Expression transformUnary(final UnaryExpression expr) {
		if (expr.getOperator() == UnaryExpression.Operator.LOGICNEG) {
			if (expr.getExpr() instanceof BinaryExpression) {
				final BinaryExpression binexp = (BinaryExpression) expr.getExpr();

				Operator newOp;

				Expression newLeft = binexp.getLeft();
				Expression newRight = binexp.getRight();

				final ILocation loc = binexp.getLocation();

				switch (binexp.getOperator()) {
				case COMPEQ:
					newOp = Operator.COMPNEQ;
					break;
				case COMPNEQ:
					newOp = Operator.COMPEQ;
					break;
				case COMPGEQ:
					newOp = Operator.COMPLT;
					break;
				case COMPGT:
					newOp = Operator.COMPLEQ;
					break;
				case COMPLEQ:
					newOp = Operator.COMPGT;
					break;
				case COMPLT:
					newOp = Operator.COMPGEQ;
					break;
				case LOGICAND:
					newOp = Operator.LOGICOR;
					newLeft = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, newLeft);
					newRight = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, newRight);
					break;
				case LOGICOR:
					newOp = Operator.LOGICAND;
					newLeft = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, newLeft);
					newRight = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, newRight);
					break;
				case LOGICIMPLIES:
					newOp = Operator.LOGICAND;
					newRight = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, newRight);
					break;
				case LOGICIFF:
					newOp = Operator.LOGICOR;
					final Expression leftLeft = newLeft;
					final Expression leftRight = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, newRight);
					final Expression rightLeft = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, newLeft);
					final Expression rightRight = newRight;
					newLeft = new BinaryExpression(loc, Operator.LOGICAND, leftLeft, leftRight);
					newRight = new BinaryExpression(loc, Operator.LOGICAND, rightLeft, rightRight);
					break;
				default:
					// Other operators can't be handled or are not valid, so just return the old expression
					return expr;
				}
				final BinaryExpression newExp = new BinaryExpression(loc, newOp, newLeft, newRight);
				return transform(newExp);
			} else if (expr.getExpr() instanceof UnaryExpression) {
				final UnaryExpression unexp = (UnaryExpression) expr.getExpr();
				if (unexp.getOperator() == UnaryExpression.Operator.LOGICNEG) {
					return transform(unexp.getExpr());
				}
			} else {
				return expr;
			}
		}
		return atomicTransform(expr);
	}

	/**
	 * Transforms a {@link BinaryExpression} to normal form Just splits conjunctions / disjunctions and uses
	 * atomicTransform then
	 */
	private Expression transformBinary(final BinaryExpression expr) {
		final Operator op = expr.getOperator();
		final Expression left = expr.getLeft();
		final Expression right = expr.getRight();

		Operator newOp = op;
		Expression newLeft = left;
		Expression newRight = right;

		final ILocation loc = expr.getLocation();

		switch (expr.getOperator()) {
		case LOGICAND:
		case LOGICOR:
			newLeft = transform(expr.getLeft());
			newRight = transform(expr.getRight());
			break;
		case LOGICIMPLIES:
			newOp = Operator.LOGICOR;
			newLeft = transform(new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, expr.getLeft()));
			newRight = transform(expr.getRight());
			break;
		case LOGICIFF:
			// x <==> y --> (x && y) || (!x && !y)
			newOp = Operator.LOGICOR;
			newLeft = transform(new BinaryExpression(loc, Operator.LOGICAND, expr.getLeft(), expr.getRight()));
			final Expression negLeft = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, expr.getLeft());
			final Expression negRight = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, expr.getRight());
			newRight = transform(new BinaryExpression(loc, Operator.LOGICAND, negLeft, negRight));
			break;
		case COMPEQ:
		case COMPNEQ:
			if (expr.getLeft().getType() instanceof PrimitiveType) {
				final PrimitiveType p = (PrimitiveType) expr.getLeft().getType();
				if (p.getTypeCode() == PrimitiveType.BOOL) {
					newLeft = transform(expr.getLeft());
					newRight = transform(expr.getRight());
				} else if (p.getTypeCode() == PrimitiveType.INT) {
					return atomicTransform(expr);
				} else {
					return expr;
				}

			} else {
				return expr;
			}
			break;
		default:
			return atomicTransform(expr);
		}
		if (newOp == op && newLeft == left && newRight == right) {
			return expr;
		}
		return new BinaryExpression(loc, newOp, newLeft, newRight);
	}

	/**
	 * Transforms an atomic expression (without logical symbols) to normal form
	 */
	private Expression atomicTransform(final Expression expr) {
		// Calculate the map + constant
		process(expr);

		if (!mIsLinear || mHasNormalForm) {
			return expr;
		}
		// Construct an expression from the map + constant
		final ILocation loc = expr.getLocation();
		Expression newExpr = null;
		for (final Entry<String, BigInteger> entry : mCoefficients.entrySet()) {
			final Expression var = mIdentifiers.get(entry.getKey());
			if (newExpr == null) {
				if (entry.getValue().equals(BigInteger.ONE)) {
					newExpr = var;
				} else if (entry.getValue().abs().equals(BigInteger.ONE)) {
					newExpr = new UnaryExpression(loc, UnaryExpression.Operator.ARITHNEGATIVE, var);
				} else {
					final Expression coeff = new IntegerLiteral(loc, entry.getValue().toString());
					newExpr = new BinaryExpression(loc, Operator.ARITHMUL, coeff, var);
				}
			} else {
				final Expression coeff = new IntegerLiteral(loc, entry.getValue().abs().toString());
				final Expression summand = new BinaryExpression(loc, Operator.ARITHMUL, coeff, var);
				final Operator operator = entry.getValue().signum() > 0 ? Operator.ARITHPLUS : Operator.ARITHMINUS;
				if (entry.getValue().abs().equals(BigInteger.ONE)) {
					newExpr = new BinaryExpression(loc, operator, newExpr, var);
				} else {
					newExpr = new BinaryExpression(loc, operator, newExpr, summand);
				}

			}
		}
		if (newExpr == null) {
			newExpr = new IntegerLiteral(loc, mConstant.toString());
		} else if (mConstant.signum() != 0) {
			final Expression constant = new IntegerLiteral(loc, mConstant.abs().toString());
			final Operator operator = mConstant.signum() > 0 ? Operator.ARITHPLUS : Operator.ARITHMINUS;
			newExpr = new BinaryExpression(loc, operator, newExpr, constant);
		}
		if (expr instanceof BinaryExpression) {
			final Operator operator = ((BinaryExpression) expr).getOperator();
			switch (operator) {
			case COMPLT:
			case COMPLEQ:
			case COMPGT:
			case COMPGEQ:
			case COMPEQ:
			case COMPNEQ:
				if (newExpr instanceof BinaryExpression && mConstant.signum() != 0) {
					// For comparison operators, the constant is on the right side (better to handle for non-zero)
					final IntegerLiteral integer = new IntegerLiteral(loc, mConstant.negate().toString());
					newExpr = new BinaryExpression(loc, operator, ((BinaryExpression) newExpr).getLeft(), integer);
				} else {
					newExpr = new BinaryExpression(loc, operator, newExpr, new IntegerLiteral(loc, "0"));
				}
				break;
			default:
				break;
			}
		}
		return newExpr;
	}

	/**
	 * Calculates the coefficients and the constant
	 */
	private void process(final Expression expr) {
		if (expr instanceof IntegerLiteral) {
			final String value = ((IntegerLiteral) expr).getValue();
			mConstant = new BigInteger(value);
			mHasNormalForm = true;
		} else if (expr instanceof IdentifierExpression) {
			final IdentifierExpression id = (IdentifierExpression) expr;
			mCoefficients.put(id.getIdentifier(), BigInteger.ONE);
			mIdentifiers.put(id.getIdentifier(), id);
			mHasNormalForm = true;
		} else if (expr instanceof UnaryExpression) {
			processUnary((UnaryExpression) expr);
		} else if (expr instanceof BinaryExpression) {
			processBinary((BinaryExpression) expr);
		} else {
			mIsLinear = false;
		}
	}

	private void processUnary(final UnaryExpression expr) {
		if (expr.getOperator() == UnaryExpression.Operator.ARITHNEGATIVE) {
			final ExpressionTransformer sub = new ExpressionTransformer();
			sub.process(expr.getExpr());
			mIdentifiers.putAll(sub.mIdentifiers);
			if (sub.mIsLinear) {
				mConstant = sub.mConstant.negate();
				for (final Entry<String, BigInteger> entry : sub.mCoefficients.entrySet()) {
					mCoefficients.put(entry.getKey(), entry.getValue().negate());
				}
				if (sub.mHasNormalForm) {
					if (sub.mCoefficients.size() == 0 && sub.mConstant.signum() > 0
							|| sub.mCoefficients.size() == 1 && sub.mConstant.signum() == 0) {
						mHasNormalForm = true;
					}
				}
			} else {
				mIsLinear = false;
			}
		}
	}

	private void processBinary(final BinaryExpression expr) {
		final ExpressionTransformer left = new ExpressionTransformer();
		left.process(expr.getLeft());
		if (!left.mIsLinear) {
			mIsLinear = false;
			return;
		}
		final ExpressionTransformer right = new ExpressionTransformer();
		right.process(expr.getRight());
		if (!right.mIsLinear) {
			mIsLinear = false;
			return;
		}

		mIdentifiers.putAll(left.mIdentifiers);
		mIdentifiers.putAll(right.mIdentifiers);

		final boolean noVarsLeft = left.mCoefficients.isEmpty();
		final boolean noVarsRight = right.mCoefficients.isEmpty();
		final Operator operator = expr.getOperator();

		switch (operator) {
		case ARITHMINUS:
		case COMPLT:
		case COMPGT:
		case COMPLEQ:
		case COMPGEQ:
		case COMPEQ:
		case COMPNEQ:
			mConstant = left.mConstant.subtract(right.mConstant);
			for (final Entry<String, BigInteger> entry : left.mCoefficients.entrySet()) {
				final BigInteger value = right.mCoefficients.get(entry.getKey());
				if (value == null) {
					mCoefficients.put(entry.getKey(), entry.getValue());
				} else {
					final BigInteger newValue = entry.getValue().subtract(value);
					if (newValue.signum() != 0) {
						mCoefficients.put(entry.getKey(), newValue);
					}
				}
			}
			for (final Entry<String, BigInteger> entry : right.mCoefficients.entrySet()) {
				if (!left.mCoefficients.containsKey(entry.getKey())) {
					mCoefficients.put(entry.getKey(), entry.getValue().negate());
				}
			}
			if (left.mHasNormalForm && right.mHasNormalForm) {
				if (left.mConstant.signum() == 0 && right.mCoefficients.isEmpty()) {
					mHasNormalForm = true;
					break;
				}
				if (right.mConstant.signum() == 0 && left.mCoefficients.isEmpty()) {
					mHasNormalForm = true;
					break;
				}
				if (operator == Operator.ARITHMINUS && left.mConstant.signum() == 0 && right.mConstant.signum() == 0) {
					mHasNormalForm = true;
					for (final String id : left.mCoefficients.keySet()) {
						if (right.mCoefficients.containsKey(id)) {
							mHasNormalForm = false;
							break;
						}
					}
				}
			}

			break;
		case ARITHPLUS:
			mConstant = left.mConstant.add(right.mConstant);
			for (final Entry<String, BigInteger> entry : left.mCoefficients.entrySet()) {
				final BigInteger value = right.mCoefficients.get(entry.getKey());
				if (value == null) {
					mCoefficients.put(entry.getKey(), entry.getValue());
				} else {
					final BigInteger newValue = entry.getValue().add(value);
					if (newValue.signum() != 0) {
						mCoefficients.put(entry.getKey(), newValue);
					}
				}
			}
			for (final Entry<String, BigInteger> entry : right.mCoefficients.entrySet()) {
				if (!left.mCoefficients.containsKey(entry.getKey())) {
					mCoefficients.put(entry.getKey(), entry.getValue());
				}
			}
			if (left.mHasNormalForm && right.mHasNormalForm) {
				if (left.mConstant.signum() == 0 && right.mCoefficients.isEmpty()) {
					mHasNormalForm = true;
					break;
				}
				if (right.mConstant.signum() == 0 && left.mCoefficients.isEmpty()) {
					mHasNormalForm = true;
					break;
				}
				if (left.mConstant.signum() == 0 && right.mConstant.signum() == 0) {
					mHasNormalForm = true;
					for (final String id : left.mCoefficients.keySet()) {
						if (right.mCoefficients.containsKey(id)) {
							mHasNormalForm = false;
							break;
						}
					}
				}
			}
			break;
		case ARITHMUL:
			if (noVarsLeft && noVarsRight) {
				mConstant = left.mConstant.multiply(right.mConstant);
			} else if (noVarsLeft) {
				if (left.mConstant.signum() == 0) {
					return;
				}
				mConstant = left.mConstant.multiply(right.mConstant);
				for (final Entry<String, BigInteger> entry : right.mCoefficients.entrySet()) {
					mCoefficients.put(entry.getKey(), entry.getValue().multiply(left.mConstant));
				}
				if (left.mHasNormalForm && right.mHasNormalForm && right.mCoefficients.size() == 1) {
					mHasNormalForm = true;
				}
			} else if (noVarsRight) {
				if (right.mConstant.signum() == 0) {
					return;
				}
				mConstant = left.mConstant.multiply(right.mConstant);
				for (final Entry<String, BigInteger> entry : left.mCoefficients.entrySet()) {
					mCoefficients.put(entry.getKey(), entry.getValue().multiply(right.mConstant));
				}
				if (left.mHasNormalForm && right.mHasNormalForm && left.mCoefficients.size() == 1) {
					mHasNormalForm = true;
				}
			} else {
				mIsLinear = false;
			}
			break;
		case ARITHMOD:
			if (noVarsLeft && noVarsRight && right.mConstant.signum() != 0) {
				mConstant = left.mConstant.mod(right.mConstant.abs());
			} else if (noVarsRight && right.mConstant.abs().equals(BigInteger.ONE)) {
				// x % +-1 = 0
				break;
			} else {
				mIsLinear = false;
			}
			break;
		case ARITHDIV:
			if (noVarsLeft && noVarsRight && right.mConstant.signum() != 0) {
				mConstant = left.mConstant.divide(right.mConstant);
				if (left.mConstant.signum() < 0) {
					if (right.mConstant.signum() > 0) {
						mConstant = mConstant.subtract(BigInteger.ONE);
					} else {
						mConstant = mConstant.add(BigInteger.ONE);
					}
				}
			} else if (noVarsRight && right.mConstant.equals(BigInteger.ONE)) {
				// x / 1 = x
				mConstant = left.mConstant;
				mCoefficients = left.mCoefficients;
			} else if (noVarsRight && right.mConstant.abs().equals(BigInteger.ONE)) {
				// x / -1 = -x
				mConstant = left.mConstant.negate();
				for (final Entry<String, BigInteger> entry : left.mCoefficients.entrySet()) {
					mCoefficients.put(entry.getKey(), entry.getValue().negate());
				}
			} else {
				mIsLinear = false;
			}
			break;
		default:
			mIsLinear = false;
			break;
		}
	}
}
