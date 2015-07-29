package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation;

import java.math.BigInteger;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizeConstants;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class IntegerTranslation extends AbstractExpressionTranslation {

	public IntegerTranslation(TypeSizeConstants m_TypeSizeConstants, FunctionDeclarations functionDeclarations) {
		super(m_TypeSizeConstants, functionDeclarations);
	}

	@Override
	public ResultExpression translateLiteral(Dispatcher main, IASTLiteralExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_char_constant:
		{
			String val = ISOIEC9899TC3.handleCharConstant(new String(node.getValue()), loc, main);
			return new ResultExpression(new RValue(new IntegerLiteral(loc, val), new CPrimitive(PRIMITIVE.CHAR)));
		}
		case IASTLiteralExpression.lk_integer_constant:
		{
			String val = new String(node.getValue());
			RValue rVal = translateIntegerLiteral(loc, val);
			return new ResultExpression(rVal);
		}
		default:
			return super.translateLiteral(main, node);
		}
	}

	@Override
	public RValue translateIntegerLiteral(ILocation loc, String val) {
		RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, false, m_TypeSizeConstants);
		return rVal;
	}

	@Override
	public Expression constructBinaryComparisonExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		BinaryExpression.Operator op;

		switch (nodeOperator) {
		case IASTBinaryExpression.op_equals:
			op = BinaryExpression.Operator.COMPEQ;
			break;
		case IASTBinaryExpression.op_greaterEqual:
			op = BinaryExpression.Operator.COMPGEQ;
			break;
		case IASTBinaryExpression.op_greaterThan:
			op = BinaryExpression.Operator.COMPGT;
			break;
		case IASTBinaryExpression.op_lessEqual:
			op = BinaryExpression.Operator.COMPLEQ;
			break;
		case IASTBinaryExpression.op_lessThan:
			op = BinaryExpression.Operator.COMPLT;
			break;
		case IASTBinaryExpression.op_notequals:
			op = BinaryExpression.Operator.COMPNEQ;
			break;
		default:
			throw new AssertionError("???");
		}
		
		return new BinaryExpression(loc, op, exp1, exp2);
	}

	@Override
	public Expression constructBinaryBitwiseShiftExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		switch (nodeOperator) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight:
		}
		
		return null;
	}

	@Override
	public Expression createArithmeticExpression(int op, Expression left, CPrimitive typeLeft,
			Expression right, CPrimitive typeRight, ILocation loc) {
		BinaryExpression.Operator operator;
		boolean bothAreIntegerLiterals = left instanceof IntegerLiteral && right instanceof IntegerLiteral;
		BigInteger leftValue = null;
		BigInteger rightValue = null;
		//TODO: add checks for UnaryExpression (otherwise we don't catch negative constants, here) --> or remove all the cases 
		//(if-then-else conditions are checked for being constant in RCFGBuilder anyway, so this is merely a decision of readability of Boogie code..)
		if (left instanceof IntegerLiteral)
			leftValue = new BigInteger(((IntegerLiteral) left).getValue());
		if (right instanceof IntegerLiteral)
			rightValue = new BigInteger(((IntegerLiteral) right).getValue());
		//TODO: make this more general, (a + 4) + 4 may still occur this way..
		String constantResult = "";
		switch (op) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
			operator = Operator.ARITHMINUS;
			if (bothAreIntegerLiterals) {
				constantResult = 
						leftValue
						.subtract(rightValue).toString();
				return new IntegerLiteral(loc, constantResult);
			} else {
				return new BinaryExpression(loc, operator, left, right);
			}
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
			operator = Operator.ARITHMUL;
			if (bothAreIntegerLiterals) {
				constantResult = 
						leftValue
							.multiply(rightValue).toString();
				return new IntegerLiteral(loc, constantResult);
			} else {
				return new BinaryExpression(loc, operator, left, right);
			}
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide:
			operator = Operator.ARITHDIV;
			/* In C the semantics of integer division is "rounding towards zero".
			 * In Boogie euclidian division is used.
			 * We translate a / b into
			 *  (a < 0) ? ( (b < 0) ? (a/b)+1 : (a/b)-1) : a/b
			 */
			if (bothAreIntegerLiterals) {
				constantResult = 
						leftValue
							.divide(rightValue).toString();
				return new IntegerLiteral(loc, constantResult);
			} else {
				BinaryExpression leftSmallerZero = new BinaryExpression(loc, 
						BinaryExpression.Operator.COMPLT, 
						left,
						new IntegerLiteral(loc, SFO.NR0));
				BinaryExpression rightSmallerZero = new BinaryExpression(loc, 
						BinaryExpression.Operator.COMPLT, 
						right,
						new IntegerLiteral(loc, SFO.NR0));
				BinaryExpression normalDivision = new BinaryExpression(loc, operator, left, right);
				if (left instanceof IntegerLiteral) {
					if (leftValue.signum() == 1) {
						return normalDivision;
					} else if (leftValue.signum() == -1) {
						return new IfThenElseExpression(loc, rightSmallerZero, 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHMINUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)), 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHPLUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)));
					} else {
						return new IntegerLiteral(loc, SFO.NR0);
					}
				} else if (right instanceof IntegerLiteral) {
					if (rightValue.signum() == 1 || rightValue.signum() == 0) {
						return new IfThenElseExpression(loc, leftSmallerZero, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalDivision, 
										new IntegerLiteral(loc, SFO.NR1)), 
								normalDivision);
					} else if (rightValue.signum() == -1) {
						return new IfThenElseExpression(loc, leftSmallerZero, 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHMINUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)), 
									normalDivision);
					} 
				} else {
					return new IfThenElseExpression(loc, leftSmallerZero, 
							new IfThenElseExpression(loc, rightSmallerZero, 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHMINUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)), 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHPLUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1))), 
						normalDivision);
				}
			}
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
			operator = Operator.ARITHMOD;
			/* In C the semantics of integer division is "rounding towards zero".
			 * In Boogie euclidian division is used.
			 * We translate a % b into
			 *  (a < 0) ? ( (b < 0) ? (a%b)-b : (a%b)+b) : a%b
			 */
			//modulo on bigInteger does not seem to follow the "multiply, add, and get the result back"-rule, together with its division..
			if (bothAreIntegerLiterals) {
				if (leftValue.signum() == 1 || leftValue.signum() == 0) {
					if (rightValue.signum() == 1) {
						constantResult = 
								leftValue.mod(rightValue).toString();
					} else if (rightValue.signum() == -1) {
						constantResult = 
								leftValue.mod(rightValue.negate()).toString();
					} else {
						constantResult = "0";
					}
				} else if (leftValue.signum() == -1) {
					if (rightValue.signum() == 1) {
						constantResult = 
								(leftValue.negate().mod(rightValue)).negate().toString();					
					} else if (rightValue.signum() == -1) {
						constantResult = 
								(leftValue.negate().mod(rightValue.negate())).negate().toString();					
					} else {
						constantResult = "0";
					}
				} 
				return new IntegerLiteral(loc, constantResult);
			} else {
				BinaryExpression leftSmallerZero = new BinaryExpression(loc, 
						BinaryExpression.Operator.COMPLT, 
						left,
						new IntegerLiteral(loc, SFO.NR0));
				BinaryExpression rightSmallerZero = new BinaryExpression(loc, 
						BinaryExpression.Operator.COMPLT, 
						right,
						new IntegerLiteral(loc, SFO.NR0));
				BinaryExpression normalModulo = new BinaryExpression(loc, operator, left, right);
				if (left instanceof IntegerLiteral) {
					if (leftValue.signum() == 1) {
						return normalModulo;
					} else if (leftValue.signum() == -1) {
						return new IfThenElseExpression(loc, rightSmallerZero, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalModulo, 
										right), 
										new BinaryExpression(loc, 
												BinaryExpression.Operator.ARITHMINUS, 
												normalModulo, 
												right));
					} else {
						return new IntegerLiteral(loc, SFO.NR0);
					}
				} else if (right instanceof IntegerLiteral) {
					if (rightValue.signum() == 1 || rightValue.signum() == 0) {
						return new IfThenElseExpression(loc, leftSmallerZero, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHMINUS, 
										normalModulo, 
										right), 
										normalModulo);
					} else if (rightValue.signum() == -1) {
						return new IfThenElseExpression(loc, leftSmallerZero, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalModulo, 
										right), 
										normalModulo);
					}
				} else {
					return new IfThenElseExpression(loc, leftSmallerZero, 
							new IfThenElseExpression(loc, rightSmallerZero, 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHPLUS, 
											normalModulo, 
											right), 
											new BinaryExpression(loc, 
													BinaryExpression.Operator.ARITHMINUS, 
													normalModulo, 
													right)), 
													normalModulo);
				}
			}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			operator = Operator.ARITHPLUS;
			if (bothAreIntegerLiterals) {
				constantResult = 
						leftValue
							.add(rightValue).toString();
				return new IntegerLiteral(loc, constantResult);
			} else {
				return new BinaryExpression(loc, operator, left, right);
			}
		default:
			String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}
}
