package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/*
 * Class to transform {@link Expression}s to an equivalent linear normal form (just used as container)
 * 
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
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
	
	/*
	 * Tranforms a given {@link Expression} to an equivalent linear normal form (if possible), w.r.t logical operators (and, or, not)
	 * Normal form: conjunctions / disjunctions of: k1 * x1 + ... + kn * xn + k0 (op 0) (where xi are variables and ki constant integers)
	 */
	public Expression transform(Expression e) {
		if (e instanceof UnaryExpression) {
			return transformUnary((UnaryExpression) e);
		}
		if (e instanceof BinaryExpression) {
			return transformBinary((BinaryExpression) e);
		}
		return atomicTransform(e);
	}

	/*
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
					newLeft = new UnaryExpression(binexp.getLocation(), UnaryExpression.Operator.LOGICNEG, newLeft);
					newRight = new UnaryExpression(binexp.getLocation(), UnaryExpression.Operator.LOGICNEG, newRight);
					break;
				case LOGICOR:
					newOp = Operator.LOGICAND;
					newLeft = new UnaryExpression(binexp.getLocation(), UnaryExpression.Operator.LOGICNEG, newLeft);
					newRight = new UnaryExpression(binexp.getLocation(), UnaryExpression.Operator.LOGICNEG, newRight);
					break;
				default:
					// Other operators can't be handled or are not valid, so just return the old expression
					return expr;
				}
				final BinaryExpression newExp = new BinaryExpression(binexp.getLocation(), newOp, newLeft, newRight);
				return transform(newExp);
			} else if (expr.getExpr() instanceof UnaryExpression) {
				final UnaryExpression unexp = (UnaryExpression) expr.getExpr();
				if (unexp.getOperator() == UnaryExpression.Operator.LOGICNEG) {
					return transform(unexp.getExpr());
				}
			}
		}
		return atomicTransform(expr);
	}
	
	/*
	 * Transforms a {@link BinaryExpression} to normal form
	 * Just splits conjunctions / disjunctions and uses atomicTransform then
	 */
	private Expression transformBinary(BinaryExpression e) {
		ExpressionTransformer left = new ExpressionTransformer();
		ExpressionTransformer right = new ExpressionTransformer();
		switch(e.getOperator()) {
		case LOGICAND:
		case LOGICOR:
			return new BinaryExpression(e.getLocation(), e.getOperator(), left.transform(e.getLeft()), right.transform(e.getRight()));
		default:
			return atomicTransform(e);
		}
	}

	/*
	 * Transforms an atomic expression (without logical symbols) to normal form
	 */
	private Expression atomicTransform(Expression e) {
		// Calculate the map + constant
		process(e);
		
		if (!mIsLinear || e == null) {
			return e;
		}
		// Construct an expression from the map + constant
		// TODO: Maybe produce "nicer" formulae (... + -1 * x -> ... - x)
		ILocation loc = e.getLocation();
		Expression newExpr = null;
		for (Map.Entry<String, BigInteger> entry : mCoefficients.entrySet()) {
			Expression var = new IdentifierExpression(loc, entry.getKey());
			Expression coeff = new IntegerLiteral(loc, entry.getValue().toString());
			Expression summand = new BinaryExpression(loc, BinaryExpression.Operator.ARITHMUL, coeff, var);
			if (newExpr == null) {
				newExpr = summand;
			} else {
				newExpr = new BinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS, newExpr, summand);
			}
		}
		Expression constant = new IntegerLiteral(loc, mConstant.toString());
		if (newExpr == null) {
			newExpr = constant;
		} else {
			newExpr = new BinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS, newExpr, constant);
		}
		if (e instanceof BinaryExpression) {
			BinaryExpression.Operator op = ((BinaryExpression) e).getOperator();
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
	
	/*
	 * 
	 */
	private void process(Expression e) {
		if (e instanceof IntegerLiteral) {
			String value = ((IntegerLiteral) e).getValue();
			mConstant = new BigInteger(value);
		} else if (e instanceof RealLiteral) {
			mIsLinear = false;
		} else if (e instanceof IdentifierExpression) {
			String varName = ((IdentifierExpression) e).getIdentifier();
			mCoefficients.put(varName, BigInteger.ONE);
		} else if (e instanceof UnaryExpression) {
			processUnary((UnaryExpression) e);
		} else if (e instanceof BinaryExpression) {
			processBinary((BinaryExpression) e);
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
