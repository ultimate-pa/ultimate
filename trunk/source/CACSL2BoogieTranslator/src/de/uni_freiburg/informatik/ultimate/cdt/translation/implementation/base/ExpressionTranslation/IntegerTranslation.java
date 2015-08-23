package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation;

import java.math.BigInteger;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.GENERALPRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UNSIGNED_TREATMENT;

public class IntegerTranslation extends AExpressionTranslation {

	private UNSIGNED_TREATMENT m_UnsignedTreatment;

	public IntegerTranslation(TypeSizes m_TypeSizeConstants, ITypeHandler typeHandler, UNSIGNED_TREATMENT unsignedTreatment) {
		super(m_TypeSizeConstants, typeHandler);
		m_UnsignedTreatment = unsignedTreatment;
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
		RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, false, m_TypeSizes);
		return rVal;
	}
	
	@Override
	public Expression constructLiteralForIntegerType(ILocation loc, CPrimitive type, BigInteger value) {
		return ISOIEC9899TC3.constructLiteralForCIntegerLiteral(loc, false, m_TypeSizes, type, value);
	}

	@Override
	public Expression constructBinaryComparisonExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
		if (!type1.equals(type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " and " + type2);
		}
		if (m_UnsignedTreatment == UNSIGNED_TREATMENT.WRAPAROUND && type1.isUnsigned()) {
			assert type2.isUnsigned();
			exp1 = applyWraparound(loc, m_TypeSizes, type1, exp1);
			exp2 = applyWraparound(loc, m_TypeSizes, type2, exp2);
		}
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
	
	public static Expression applyWraparound(ILocation loc, TypeSizes typeSizes, CPrimitive cPrimitive, Expression operand) {
		if (cPrimitive.getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
			if (cPrimitive.isUnsigned()) {
				BigInteger maxValuePlusOne = typeSizes.getMaxValueOfPrimitiveType(cPrimitive).add(BigInteger.ONE);
				return new BinaryExpression(loc, BinaryExpression.Operator.ARITHMOD, 
						operand, 
						new IntegerLiteral(loc, maxValuePlusOne.toString()));
			} else {
				throw new AssertionError("wraparound only for unsigned types");
			}
		} else {
			throw new AssertionError("wraparound only for integer types");
		}
	}

	@Override
	public Expression constructBinaryBitwiseExpression(ILocation loc,
			int op, Expression left, CPrimitive typeLeft,
			Expression right, CPrimitive typeRight) {
		final String funcname;
		switch (op) {
		case IASTBinaryExpression.op_binaryAnd:
			funcname = "bitwiseAnd";
			break;
		case IASTBinaryExpression.op_binaryOr:
			funcname = "bitwiseOr";
			break;
		case IASTBinaryExpression.op_binaryXor:
			funcname = "bitwiseXor";
			break;
		case IASTBinaryExpression.op_shiftLeft:
			funcname = "shiftLeft";
			break;
		case IASTBinaryExpression.op_shiftRight:
			funcname = "shiftRight";
			break;
		default:
			String msg = "Unknown or unsupported bitwise expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, false, (CPrimitive) typeLeft, (CPrimitive) typeLeft, (CPrimitive) typeRight);
		Expression func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, new Expression[]{left, right});
		return func;
	}
	
	@Override
	public Expression constructUnaryExpression(ILocation loc,
			int op, Expression expr, CPrimitive type) {
		final Expression result;
		switch (op) {
		case IASTUnaryExpression.op_tilde:
			final String funcname = "bitwiseComplement";
			declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, false, type, type);
			result = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, new Expression[]{expr});
			break;
		case IASTUnaryExpression.op_minus:
			result = new UnaryExpression(loc, UnaryExpression.Operator.ARITHNEGATIVE, expr);
			break;
		default:
			String msg = "Unknown or unsupported bitwise expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		return result;
	}
	
	private void declareBitvectorFunction(ILocation loc, String prefixedFunctionName,
			boolean boogieResultTypeBool, CPrimitive resultCType, CPrimitive... paramCType) {
		String functionName = prefixedFunctionName.substring(1, prefixedFunctionName.length());
		Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName) });
		Attribute[] attributes = new Attribute[] { attribute };
		m_FunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + functionName, attributes, boogieResultTypeBool, resultCType, paramCType);
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
			 *  (a < 0 && a%b != 0) ? ( (b < 0) ? (a/b)+1 : (a/b)-1) : a/b
			 */
			if (bothAreIntegerLiterals) {
				constantResult = 
						leftValue
							.divide(rightValue).toString();
				return new IntegerLiteral(loc, constantResult);
			} else {
				BinaryExpression leftSmallerZeroAndThereIsRemainder;
				{
					BinaryExpression leftModRight = new BinaryExpression(loc, Operator.ARITHMOD, left, right);
					BinaryExpression thereIsRemainder = new BinaryExpression(loc, 
							Operator.COMPNEQ, leftModRight, new IntegerLiteral(loc, SFO.NR0));
					BinaryExpression leftSmallerZero = new BinaryExpression(loc, 
							BinaryExpression.Operator.COMPLT, 
							left,
							new IntegerLiteral(loc, SFO.NR0));
					leftSmallerZeroAndThereIsRemainder = 
							new BinaryExpression(loc, Operator.LOGICAND, leftSmallerZero, thereIsRemainder);
				}
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
						return new IfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalDivision, 
										new IntegerLiteral(loc, SFO.NR1)), 
								normalDivision);
					} else if (rightValue.signum() == -1) {
						return new IfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHMINUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)), 
									normalDivision);
					} 
				} else {
					return new IfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
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
			 *  (a < 0 && a%b != 0) ? ( (b < 0) ? (a%b)-b : (a%b)+b) : a%b
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
				BinaryExpression leftSmallerZeroAndThereIsRemainder;
				{
					BinaryExpression leftModRight = new BinaryExpression(loc, Operator.ARITHMOD, left, right);
					BinaryExpression thereIsRemainder = new BinaryExpression(loc, 
							Operator.COMPNEQ, leftModRight, new IntegerLiteral(loc, SFO.NR0));
					BinaryExpression leftSmallerZero = new BinaryExpression(loc, 
							BinaryExpression.Operator.COMPLT, 
							left,
							new IntegerLiteral(loc, SFO.NR0));
					leftSmallerZeroAndThereIsRemainder = 
							new BinaryExpression(loc, Operator.LOGICAND, leftSmallerZero, thereIsRemainder);
				}
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
						return new IfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHMINUS, 
										normalModulo, 
										right), 
										normalModulo);
					} else if (rightValue.signum() == -1) {
						return new IfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalModulo, 
										right), 
										normalModulo);
					}
				} else {
					return new IfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
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
	
	

	@Override
	public void convert(ILocation loc, ResultExpression operand,
			CType resultType, TypeSizes typeSizes) {
		if (m_UnsignedTreatment == UNSIGNED_TREATMENT.ASSUME_ALL) {
			BigInteger maxValuePlusOne = typeSizes.getMaxValueOfPrimitiveType((CPrimitive) resultType).add(BigInteger.ONE);
			AssumeStatement assumeGeq0 = new AssumeStatement(loc, new BinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
					operand.lrVal.getValue(), new IntegerLiteral(loc, SFO.NR0)));
			operand.stmt.add(assumeGeq0);

			AssumeStatement assumeLtMax = new AssumeStatement(loc, new BinaryExpression(loc, BinaryExpression.Operator.COMPLT,
					operand.lrVal.getValue(), new IntegerLiteral(loc, maxValuePlusOne.toString())));
			operand.stmt.add(assumeLtMax);
		} else {
			// do nothing
		}
		
		// set the type of the operand to resultType
		operand.lrVal.cType = resultType;
	}

}
