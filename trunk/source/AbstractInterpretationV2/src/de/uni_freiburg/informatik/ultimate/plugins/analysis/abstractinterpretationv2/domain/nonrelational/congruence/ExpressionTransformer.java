package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Class to transform {@link Expression}s to an equivalent linear normal form (just used as container)
 * 
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * 
 */
public class ExpressionTransformer {
	private BigInteger mConstant;
	private HashMap<String, BigInteger> mCoefficients;
	private boolean mIsLinear;
	
	public ExpressionTransformer() {
		mConstant = BigInteger.ZERO;
		mCoefficients = new HashMap<>();
		mIsLinear = true;
	}
	
	/**
	 * Tranforms a given {@link Expression} to an equivalent linear normal form (if possible), w.r.t logical operators
	 * Normal form: conjunctions / disjunctions of: k1 * x1 + ... + kn * xn + k0 (op 0) (where xi are variables and ki constant integers)
	 */
	public Expression transform(Expression e) {
		if (e instanceof UnaryExpression) {
			return transformUnary((UnaryExpression) e);
		}
		if (e instanceof BinaryExpression) {
			return transformBinary((BinaryExpression) e);
		}
		return e;
	}

	/**
	 * Transforms a {@link UnaryExpression} to normal form
	 * Just moves the not inside and uses atomicTransform
	 */
	private Expression transformUnary(UnaryExpression expr) {
		if (expr.getOperator() == UnaryExpression.Operator.LOGICNEG) {
			if (expr.getExpr() instanceof BinaryExpression) {
				final BinaryExpression binexp = (BinaryExpression) expr.getExpr();

				Operator newOp;

				Expression newLeft = binexp.getLeft();
				Expression newRight = binexp.getRight();
				
				ILocation loc = binexp.getLocation();

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
					Expression leftLeft = newLeft;
					Expression leftRight = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, newRight);
					Expression rightLeft = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, newLeft);
					Expression rightRight = newRight;
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
	 * Transforms a {@link BinaryExpression} to normal form
	 * Just splits conjunctions / disjunctions and uses atomicTransform then
	 */
	private Expression transformBinary(BinaryExpression e) {
		Operator newOp = e.getOperator();
		
		Expression newLeft = e.getLeft();
		Expression newRight = e.getRight();
		
		ExpressionTransformer left = new ExpressionTransformer();
		ExpressionTransformer right = new ExpressionTransformer();
		
		ILocation loc = e.getLocation();
		
		switch(e.getOperator()) {
		case LOGICAND:
		case LOGICOR:
			newLeft = left.transform(e.getLeft());
			newRight = right.transform(e.getRight());
			break;
		case LOGICIMPLIES:
			newOp = Operator.LOGICOR;
			newLeft = left.transform(new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, e.getLeft()));
			newRight = right.transform(e.getRight());
			break;
		case LOGICIFF:
			// x <==> y --> (x && y) || (!x && !y)
			newOp = Operator.LOGICOR;
			newLeft = left.transform(new BinaryExpression(loc, Operator.LOGICAND, e.getLeft(), e.getRight()));		
			Expression negLeft = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, e.getLeft());
			Expression negRight = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, e.getRight());
			newRight = right.transform(new BinaryExpression(loc, Operator.LOGICAND, negLeft, negRight));
			break;
		case COMPEQ:
		case COMPNEQ:
			if (e.getLeft().getType() instanceof PrimitiveType) {
				PrimitiveType p = (PrimitiveType) e.getLeft().getType();
				if (p.getTypeCode() == PrimitiveType.BOOL) {
					newLeft = left.transform(e.getLeft());
					newRight = right.transform(e.getRight());
				} else if (p.getTypeCode() == PrimitiveType.INT) {
					return atomicTransform(e);
				} else {
					return e;
				}
				
			} else {
				return e;
			}
			break;
		default:
			return atomicTransform(e);
		}
		return new BinaryExpression(loc, newOp, newLeft, newRight);
	}

	/**
	 * Transforms an atomic expression (without logical symbols) to normal form
	 */
	private Expression atomicTransform(Expression e) {
		// Calculate the map + constant
		process(e);
		
		if (!mIsLinear || e == null) {
			return e;
		}
		// Construct an expression from the map + constant
		ILocation loc = e.getLocation();
		Expression newExpr = null;
		for (Map.Entry<String, BigInteger> entry : mCoefficients.entrySet()) {
			if (newExpr == null) {
				Expression var = new IdentifierExpression(loc, entry.getKey());
				if (entry.getValue().equals(BigInteger.ONE)) {
					newExpr = var;
				} else if (entry.getValue().abs().equals(BigInteger.ONE)) {
					newExpr = new UnaryExpression(loc, UnaryExpression.Operator.ARITHNEGATIVE, var);
				} else {
					Expression coeff = new IntegerLiteral(loc, entry.getValue().toString());
					newExpr = new BinaryExpression(loc, Operator.ARITHMUL, coeff, var);
				}
			} else {
				Expression var = new IdentifierExpression(loc, entry.getKey());
				Expression coeff = new IntegerLiteral(loc, entry.getValue().abs().toString());
				Expression summand = new BinaryExpression(loc, Operator.ARITHMUL, coeff, var);
				Operator op = entry.getValue().signum() > 0 ? Operator.ARITHPLUS : Operator.ARITHMINUS;
				if (entry.getValue().abs().equals(BigInteger.ONE)) {
					newExpr = new BinaryExpression(loc, op, newExpr, var);
				} else {
					newExpr = new BinaryExpression(loc, op, newExpr, summand);
				}
				
			}
		}
		if (newExpr == null) {
			newExpr = new IntegerLiteral(loc, mConstant.toString());;
		} else if (mConstant.signum() != 0) {
			Expression constant = new IntegerLiteral(loc, mConstant.abs().toString());
			Operator op = mConstant.signum() > 0 ? Operator.ARITHPLUS : Operator.ARITHMINUS;
			newExpr = new BinaryExpression(loc, op, newExpr, constant);
		}
		if (e instanceof BinaryExpression) {
			Operator op = ((BinaryExpression) e).getOperator();
			switch (op) {
				case COMPLT:
				case COMPGT:
				case COMPLEQ:
				case COMPGEQ:
				case COMPEQ:
				case COMPNEQ:
					newExpr = new BinaryExpression(loc, op, newExpr, new IntegerLiteral(loc, "0"));	
				default:
					break;
			}
		}
		return newExpr;
	}
	
	/**
	 *  Calculates the coefficients and the constant
	 */
	private void process(Expression e) {
		if (e instanceof IntegerLiteral) {
			String value = ((IntegerLiteral) e).getValue();
			mConstant = new BigInteger(value);
		} else if (e instanceof IdentifierExpression) {
			String varName = ((IdentifierExpression) e).getIdentifier();
			mCoefficients.put(varName, BigInteger.ONE);
		} else if (e instanceof UnaryExpression) {
			processUnary((UnaryExpression) e);
		} else if (e instanceof BinaryExpression) {
			processBinary((BinaryExpression) e);
		} else {
			mIsLinear = false;
		}
	}
	
	private void processUnary(UnaryExpression e) {
		if (e.getOperator() == UnaryExpression.Operator.ARITHNEGATIVE) {
			ExpressionTransformer sub = new ExpressionTransformer();
			sub.process(e.getExpr());
			if (sub.mIsLinear) {
				mConstant = sub.mConstant.negate();
				for (Map.Entry<String, BigInteger> entry : sub.mCoefficients.entrySet()) {
					mCoefficients.put(entry.getKey(), entry.getValue().negate());
				}
			}
		}
	}
	
	private void processBinary(BinaryExpression e) {
		ExpressionTransformer left = new ExpressionTransformer();
		left.process(e.getLeft());
		if (!left.mIsLinear) {
			mIsLinear = false;
			return;
		}
		ExpressionTransformer right = new ExpressionTransformer();
		right.process(e.getRight());
		if (!right.mIsLinear) {
			mIsLinear = false;
			return;
		}
		
		int sLeft = left.mCoefficients.size();
		int sRight = right.mCoefficients.size();
		
		switch (e.getOperator()) {
			case ARITHMINUS:
			case COMPLT:
			case COMPGT:
			case COMPLEQ:
			case COMPGEQ:
			case COMPEQ:
			case COMPNEQ:
				mConstant = left.mConstant.subtract(right.mConstant);
				for (Map.Entry<String, BigInteger> entry : left.mCoefficients.entrySet()) {
					BigInteger value = right.mCoefficients.get(entry.getKey());
					if (value == null) {
						mCoefficients.put(entry.getKey(), entry.getValue());
					} else {
						BigInteger newValue = entry.getValue().subtract(value);
						if (newValue.signum() != 0) {
							mCoefficients.put(entry.getKey(), newValue);
						}
					}
				}
				for (Map.Entry<String, BigInteger> entry : right.mCoefficients.entrySet()) {
					if (!left.mCoefficients.containsKey(entry.getKey())) {
						mCoefficients.put(entry.getKey(), entry.getValue().negate());
					}
				}
				break;
			case ARITHPLUS:
				mConstant = left.mConstant.add(right.mConstant);
				for (Map.Entry<String, BigInteger> entry : left.mCoefficients.entrySet()) {
					BigInteger value = right.mCoefficients.get(entry.getKey());
					if (value == null) {
						mCoefficients.put(entry.getKey(), entry.getValue());
					} else {
						BigInteger newValue = entry.getValue().add(value);
						if (newValue.signum() != 0) {
							mCoefficients.put(entry.getKey(), newValue);
						}
					}
				}
				for (Map.Entry<String, BigInteger> entry : right.mCoefficients.entrySet()) {
					if (!left.mCoefficients.containsKey(entry.getKey())) {
						mCoefficients.put(entry.getKey(), entry.getValue());
					}
				}
				break;
			case ARITHMUL:
				if (sLeft == 0 && sRight == 0) {
					mConstant = left.mConstant.multiply(right.mConstant);
				} else if (sLeft == 0) {
					if (left.mConstant.signum() == 0) { return; }
					mConstant = left.mConstant.multiply(right.mConstant);
					for (Map.Entry<String, BigInteger> entry : right.mCoefficients.entrySet()) {
						mCoefficients.put(entry.getKey(), entry.getValue().multiply(left.mConstant));
					}
				} else if (sRight == 0) {
					if (right.mConstant.signum() == 0) { return; }
					mConstant = left.mConstant.multiply(right.mConstant);
					for (Map.Entry<String, BigInteger> entry : left.mCoefficients.entrySet()) {
						mCoefficients.put(entry.getKey(), entry.getValue().multiply(right.mConstant));
					}
				} else {
					mIsLinear = false;
				}
				break;
			case ARITHMOD:
				if (sLeft == 0 && sRight == 0 && right.mConstant.signum() != 0) {
					mConstant = left.mConstant.mod(right.mConstant.abs());
				} else if (sRight == 0 && right.mConstant.abs().equals(BigInteger.ONE)){
					// x % +-1 = 0
					break;
				} else {
					mIsLinear = false;
				}
				break;
			case ARITHDIV:
				if (sLeft == 0 && sRight == 0 && right.mConstant.signum() != 0) {
					mConstant = left.mConstant.divide(right.mConstant);
					if (left.mConstant.signum() < 0) {
						if (right.mConstant.signum() > 0) {
							mConstant = mConstant.subtract(BigInteger.ONE);
						} else {
							mConstant = mConstant.add(BigInteger.ONE);
						}
					}
				} else if (sRight == 0 && right.mConstant.equals(BigInteger.ONE)){
					// x / 1 = x
					mConstant = left.mConstant;
					mCoefficients = left.mCoefficients;
				} else if (sRight == 0 && right.mConstant.negate().equals(BigInteger.ONE)){
					// x / -1 = -x
					mConstant = left.mConstant.negate();
					for (Map.Entry<String, BigInteger> entry : left.mCoefficients.entrySet()) {
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
