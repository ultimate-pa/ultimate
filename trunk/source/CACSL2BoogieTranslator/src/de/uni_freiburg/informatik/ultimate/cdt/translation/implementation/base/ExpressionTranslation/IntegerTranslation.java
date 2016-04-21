/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Thomas Lang
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation;

import java.math.BigInteger;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.GENERALPRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_INTEGER_CONVERSION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UNSIGNED_TREATMENT;

public class IntegerTranslation extends AExpressionTranslation {

	private UNSIGNED_TREATMENT m_UnsignedTreatment;
	private final boolean m_OverapproximateIntPointerConversion = true;
	
	/**
	 * Add assume statements that state that values of signed integer types are 
	 * in range.
	 */
	private final boolean m_AssumeThatSignedValuesAreInRange;

	public IntegerTranslation(TypeSizes m_TypeSizeConstants, ITypeHandler typeHandler, UNSIGNED_TREATMENT unsignedTreatment, boolean assumeSignedInRange, 
			POINTER_INTEGER_CONVERSION pointerIntegerConversion) {
		super(m_TypeSizeConstants, typeHandler, pointerIntegerConversion);
		m_UnsignedTreatment = unsignedTreatment;
		m_AssumeThatSignedValuesAreInRange = assumeSignedInRange;
	}

	@Override
	public ExpressionResult translateLiteral(Dispatcher main, IASTLiteralExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_char_constant:
		{
			String val = ISOIEC9899TC3.handleCharConstant(new String(node.getValue()), loc, main);
			return new ExpressionResult(new RValue(new IntegerLiteral(loc, val), new CPrimitive(PRIMITIVE.CHAR)));
		}
		case IASTLiteralExpression.lk_integer_constant:
		{
			String val = new String(node.getValue());
			RValue rVal = translateIntegerLiteral(loc, val);
			return new ExpressionResult(rVal);
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
	public RValue translateFloatingLiteral(ILocation loc, String val) {
		RValue rVal = ISOIEC9899TC3.handleFloatConstant(val, loc, true, m_TypeSizes, m_FunctionDeclarations);
		return rVal;
	}

	@Override
	public Expression constructBinaryComparisonIntegerExpression(ILocation loc, int nodeOperator, Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2) {
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
		
		return ExpressionFactory.newBinaryExpression(loc, op, exp1, exp2);
	}
	
	public static Expression applyWraparound(ILocation loc, TypeSizes typeSizes, CPrimitive cPrimitive, Expression operand) {
		if (cPrimitive.getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
			if (cPrimitive.isUnsigned()) {
				BigInteger maxValuePlusOne = typeSizes.getMaxValueOfPrimitiveType(cPrimitive).add(BigInteger.ONE);
				return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMOD, 
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
	public Expression constructBinaryBitwiseIntegerExpression(ILocation loc,
			int op, Expression left, CPrimitive typeLeft,
			Expression right, CPrimitive typeRight) {
		final String funcname;
		switch (op) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryAndAssign:
			funcname = "bitwiseAnd";
			break;
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryOrAssign:
			funcname = "bitwiseOr";
			break;
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryXorAssign:
			funcname = "bitwiseXor";
			break;
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftLeftAssign:
			funcname = "shiftLeft";
			break;
		case IASTBinaryExpression.op_shiftRight:
		case IASTBinaryExpression.op_shiftRightAssign:
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
	public Expression constructUnaryIntegerExpression(ILocation loc,
			int op, Expression expr, CPrimitive type) {
		final Expression result;
		switch (op) {
		case IASTUnaryExpression.op_tilde:
			final String funcname = "bitwiseComplement";
			declareBitvectorFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, false, type, type);
			result = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + funcname, new Expression[]{expr});
			break;
		case IASTUnaryExpression.op_minus: {
			if (type.getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
				result = ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.ARITHNEGATIVE, expr);
			} else if (type.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) {
				//TODO: having boogie deal with negative real literals would be the nice solution..
				result = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMINUS, new RealLiteral(loc, "0.0"), expr);		
			} else {
				throw new IllegalArgumentException("unsupported " + type);
			}
		}
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
	public Expression constructArithmeticIntegerExpression(ILocation loc, int nodeOperator, Expression exp1,
			CPrimitive type1, Expression exp2, CPrimitive type2) {
		assert (type1.getGeneralType() == GENERALPRIMITIVE.INTTYPE);
		assert (type2.getGeneralType() == GENERALPRIMITIVE.INTTYPE);
		BinaryExpression.Operator operator;
		if (type1.isIntegerType() && type1.isUnsigned()) {
			assert type2.isIntegerType() && type2.isUnsigned() : "incompatible types";
			if (nodeOperator == IASTBinaryExpression.op_divide || 
					nodeOperator == IASTBinaryExpression.op_divide || 
					nodeOperator == IASTBinaryExpression.op_modulo || 
					nodeOperator == IASTBinaryExpression.op_moduloAssign) {
				// apply wraparound to ensure that Nutz transformation is sound
				// (see examples/programs/regression/c/NutzTransformation02.c)
				exp1 = applyWraparound(loc, m_TypeSizes, type1, exp1);
				exp2 = applyWraparound(loc, m_TypeSizes, type2, exp2);
			}
		}
		boolean bothAreIntegerLiterals = exp1 instanceof IntegerLiteral && exp2 instanceof IntegerLiteral;
		BigInteger leftValue = null;
		BigInteger rightValue = null;
		//TODO: add checks for UnaryExpression (otherwise we don't catch negative constants, here) --> or remove all the cases 
		//(if-then-else conditions are checked for being constant in RCFGBuilder anyway, so this is merely a decision of readability of Boogie code..)
		if (exp1 instanceof IntegerLiteral)
			leftValue = new BigInteger(((IntegerLiteral) exp1).getValue());
		if (exp2 instanceof IntegerLiteral)
			rightValue = new BigInteger(((IntegerLiteral) exp2).getValue());
		//TODO: make this more general, (a + 4) + 4 may still occur this way..
		String constantResult = "";
		switch (nodeOperator) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
			operator = Operator.ARITHMINUS;
			if (bothAreIntegerLiterals) {
				constantResult = 
						leftValue
						.subtract(rightValue).toString();
				return new IntegerLiteral(loc, constantResult);
			} else {
				return ExpressionFactory.newBinaryExpression(loc, operator, exp1, exp2);
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
				return ExpressionFactory.newBinaryExpression(loc, operator, exp1, exp2);
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
				Expression leftSmallerZeroAndThereIsRemainder;
				{
					Expression leftModRight = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMOD, exp1, exp2);
					Expression thereIsRemainder = ExpressionFactory.newBinaryExpression(loc, 
							Operator.COMPNEQ, leftModRight, new IntegerLiteral(loc, SFO.NR0));
					Expression leftSmallerZero = ExpressionFactory.newBinaryExpression(loc, 
							BinaryExpression.Operator.COMPLT, 
							exp1,
							new IntegerLiteral(loc, SFO.NR0));
					leftSmallerZeroAndThereIsRemainder = 
							ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftSmallerZero, thereIsRemainder);
				}
				Expression rightSmallerZero = ExpressionFactory.newBinaryExpression(loc, 
						BinaryExpression.Operator.COMPLT, 
						exp2,
						new IntegerLiteral(loc, SFO.NR0));
				Expression normalDivision = ExpressionFactory.newBinaryExpression(loc, operator, exp1, exp2);
				if (exp1 instanceof IntegerLiteral) {
					if (leftValue.signum() == 1) {
						return normalDivision;
					} else if (leftValue.signum() == -1) {
						return ExpressionFactory.newIfThenElseExpression(loc, rightSmallerZero, 
									ExpressionFactory.newBinaryExpression(loc, 
											BinaryExpression.Operator.ARITHMINUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)), 
									ExpressionFactory.newBinaryExpression(loc, 
											BinaryExpression.Operator.ARITHPLUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)));
					} else {
						return new IntegerLiteral(loc, SFO.NR0);
					}
				} else if (exp2 instanceof IntegerLiteral) {
					if (rightValue.signum() == 1 || rightValue.signum() == 0) {
						return ExpressionFactory.newIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
								ExpressionFactory.newBinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalDivision, 
										new IntegerLiteral(loc, SFO.NR1)), 
								normalDivision);
					} else if (rightValue.signum() == -1) {
						return ExpressionFactory.newIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
									ExpressionFactory.newBinaryExpression(loc, 
											BinaryExpression.Operator.ARITHMINUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)), 
									normalDivision);
					} 
				} else {
					return ExpressionFactory.newIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
							ExpressionFactory.newIfThenElseExpression(loc, rightSmallerZero, 
									ExpressionFactory.newBinaryExpression(loc, 
											BinaryExpression.Operator.ARITHMINUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)), 
									ExpressionFactory.newBinaryExpression(loc, 
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
				Expression leftSmallerZeroAndThereIsRemainder;
				{
					Expression leftModRight = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMOD, exp1, exp2);
					Expression thereIsRemainder = ExpressionFactory.newBinaryExpression(loc, 
							Operator.COMPNEQ, leftModRight, new IntegerLiteral(loc, SFO.NR0));
					Expression leftSmallerZero = ExpressionFactory.newBinaryExpression(loc, 
							BinaryExpression.Operator.COMPLT, 
							exp1,
							new IntegerLiteral(loc, SFO.NR0));
					leftSmallerZeroAndThereIsRemainder = 
							ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftSmallerZero, thereIsRemainder);
				}
				Expression rightSmallerZero = ExpressionFactory.newBinaryExpression(loc, 
						BinaryExpression.Operator.COMPLT, 
						exp2,
						new IntegerLiteral(loc, SFO.NR0));
				Expression normalModulo = ExpressionFactory.newBinaryExpression(loc, operator, exp1, exp2);
				if (exp1 instanceof IntegerLiteral) {
					if (leftValue.signum() == 1) {
						return normalModulo;
					} else if (leftValue.signum() == -1) {
						return ExpressionFactory.newIfThenElseExpression(loc, rightSmallerZero, 
								ExpressionFactory.newBinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalModulo, 
										exp2), 
										ExpressionFactory.newBinaryExpression(loc, 
												BinaryExpression.Operator.ARITHMINUS, 
												normalModulo, 
												exp2));
					} else {
						return new IntegerLiteral(loc, SFO.NR0);
					}
				} else if (exp2 instanceof IntegerLiteral) {
					if (rightValue.signum() == 1 || rightValue.signum() == 0) {
						return ExpressionFactory.newIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
								ExpressionFactory.newBinaryExpression(loc, 
										BinaryExpression.Operator.ARITHMINUS, 
										normalModulo, 
										exp2), 
										normalModulo);
					} else if (rightValue.signum() == -1) {
						return ExpressionFactory.newIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
								ExpressionFactory.newBinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalModulo, 
										exp2), 
										normalModulo);
					}
				} else {
					return ExpressionFactory.newIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder, 
							ExpressionFactory.newIfThenElseExpression(loc, rightSmallerZero, 
									ExpressionFactory.newBinaryExpression(loc, 
											BinaryExpression.Operator.ARITHPLUS, 
											normalModulo, 
											exp2), 
											ExpressionFactory.newBinaryExpression(loc, 
													BinaryExpression.Operator.ARITHMINUS, 
													normalModulo, 
													exp2)), 
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
				return ExpressionFactory.newBinaryExpression(loc, operator, exp1, exp2);
			}
		default:
			String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}
	
	

	@Override
	public void convertIntToInt_NonBool(ILocation loc, ExpressionResult operand,
			CPrimitive resultType) {
		if (resultType.isIntegerType()) {
			convertToIntegerType(loc, operand, resultType);
		} else {
			throw new UnsupportedOperationException("not yet supported: conversion to " + resultType);
		}
	}

	private void convertToIntegerType(ILocation loc, ExpressionResult operand,
			CPrimitive resultType) {
		assert resultType.isIntegerType();
		CPrimitive oldType = (CPrimitive) operand.lrVal.getCType();
		if (oldType.isIntegerType()) {
			final Expression newExpression;
			if (resultType.isUnsigned()) {
				final Expression old_WrapedIfNeeded;
				if (oldType.isUnsigned() && 
						m_TypeSizes.getSize(resultType.getType()) > m_TypeSizes.getSize(oldType.getType())) {
					// required for sound Nutz transformation 
					// (see examples/programs/regression/c/NutzTransformation03.c)
					old_WrapedIfNeeded = applyWraparound(loc, m_TypeSizes, oldType, operand.lrVal.getValue());
				} else {
					old_WrapedIfNeeded = operand.lrVal.getValue();
				}
				if (m_UnsignedTreatment == UNSIGNED_TREATMENT.ASSUME_ALL) {
					BigInteger maxValuePlusOne = m_TypeSizes.getMaxValueOfPrimitiveType((CPrimitive) resultType).add(BigInteger.ONE);
					AssumeStatement assumeGeq0 = new AssumeStatement(loc, ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
							old_WrapedIfNeeded, new IntegerLiteral(loc, SFO.NR0)));
					operand.stmt.add(assumeGeq0);

					AssumeStatement assumeLtMax = new AssumeStatement(loc, ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
							old_WrapedIfNeeded, new IntegerLiteral(loc, maxValuePlusOne.toString())));
					operand.stmt.add(assumeLtMax);
				} else {
					// do nothing
				}
				newExpression = old_WrapedIfNeeded;
			} else {
				assert !resultType.isUnsigned();
				final Expression old_WrapedIfUnsigned;
				if (oldType.isUnsigned()) {
					// required for sound Nutz transformation 
					// (see examples/programs/regression/c/NutzTransformation01.c)
					old_WrapedIfUnsigned = applyWraparound(loc, m_TypeSizes, oldType, operand.lrVal.getValue());
				} else {
					old_WrapedIfUnsigned = operand.lrVal.getValue();
				}
				if (m_TypeSizes.getSize(resultType.getType()) > m_TypeSizes.getSize(oldType.getType()) || 
						m_TypeSizes.getSize(resultType.getType()) == m_TypeSizes.getSize(oldType.getType()) && !oldType.isUnsigned() ) {
					newExpression = old_WrapedIfUnsigned;
				} else {
					// According to C11 6.3.1.3.3 the result is implementation-defined
					// it the value cannot be represented by the new type
					// We have chosen an implementation that is similar to 
					// taking the lowest bits in a two's complement representation:
					// First we take the value modulo the cardinality of the
					// data range (which is 2*(MAX_VALUE+1) for signed )
					// If the number is strictly larger than MAX_VALUE we 
					// subtract the cardinality of the data range.
					CPrimitive correspondingUnsignedType = resultType.getCorrespondingUnsignedType(); 
					Expression wrapped = applyWraparound(loc, m_TypeSizes, correspondingUnsignedType, old_WrapedIfUnsigned);
					Expression maxValue = constructLiteralForIntegerType(loc, oldType, m_TypeSizes.getMaxValueOfPrimitiveType(resultType));
					Expression condition = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, wrapped, maxValue);
					Expression range = constructLiteralForIntegerType(loc, oldType, m_TypeSizes.getMaxValueOfPrimitiveType(correspondingUnsignedType).add(BigInteger.ONE));
					newExpression = ExpressionFactory.newIfThenElseExpression(loc, condition, 
							wrapped, 
							ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMINUS, wrapped, range));
				}

			}
			RValue newRValue = new RValue(newExpression, resultType, false, false);
			operand.lrVal = newRValue;
		} else {
			throw new UnsupportedOperationException("not yet supported: conversion from " + oldType);
		}
	}

	public void old_convertPointerToInt(ILocation loc,
			ExpressionResult rexp, CPrimitive newType) {
		assert (newType.isIntegerType());
		assert (rexp.lrVal.getCType() instanceof CPointer);
		if (m_OverapproximateIntPointerConversion) {
			super.convertPointerToInt(loc, rexp, newType);
		} else {
			final Expression pointerExpression = rexp.lrVal.getValue();
			final Expression intExpression;
			if (m_TypeSizes.useFixedTypeSizes()) {
				BigInteger maxPtrValuePlusOne = m_TypeSizes.getMaxValueOfPointer().add(BigInteger.ONE); 
				IntegerLiteral max_Pointer = new IntegerLiteral(loc, maxPtrValuePlusOne.toString());
				intExpression = constructArithmeticExpression(loc,
						IASTBinaryExpression.op_plus,
						constructArithmeticExpression(loc, 
								IASTBinaryExpression.op_multiply, 
								MemoryHandler.getPointerBaseAddress(pointerExpression,  loc), newType, 
								max_Pointer, newType), newType, 
						MemoryHandler.getPointerOffset(pointerExpression, loc), newType);
			} else {
				intExpression = MemoryHandler.getPointerOffset(pointerExpression, loc);
			}
			RValue rValue = new RValue(intExpression, newType, false, true);
			rexp.lrVal = rValue;
		}
	}

	public void old_convertIntToPointer(ILocation loc,
			ExpressionResult rexp, CPointer newType) {
		if (m_OverapproximateIntPointerConversion) {
			super.convertIntToPointer(loc, rexp, newType);
		} else {
			final Expression intExpression = rexp.lrVal.getValue();
			final Expression baseAdress;
			final Expression offsetAdress;
			if (m_TypeSizes.useFixedTypeSizes()) {
				BigInteger maxPtrValuePlusOne = m_TypeSizes.getMaxValueOfPointer().add(BigInteger.ONE); 
				IntegerLiteral max_Pointer = new IntegerLiteral(loc, maxPtrValuePlusOne.toString());
				baseAdress = constructArithmeticExpression(loc,
								IASTBinaryExpression.op_divide,
								intExpression, getCTypeOfPointerComponents(), 
								max_Pointer, getCTypeOfPointerComponents());
				offsetAdress = constructArithmeticExpression(loc,
										IASTBinaryExpression.op_modulo,
										intExpression, getCTypeOfPointerComponents(), 
										max_Pointer, getCTypeOfPointerComponents());
			} else {
				baseAdress = constructLiteralForIntegerType(loc, getCTypeOfPointerComponents(), BigInteger.ZERO);
				offsetAdress = intExpression;
			}
			final Expression pointerExpression = MemoryHandler.constructPointerFromBaseAndOffset(baseAdress, offsetAdress, loc);
			RValue rValue = new RValue(pointerExpression, newType, false, false);
			rexp.lrVal = rValue;
		}
	}
	
	@Override
	public BigInteger extractIntegerValue(Expression expr, CType cType) {
		if (cType.isIntegerType()) {
			if (expr instanceof IntegerLiteral) {
				BigInteger value =  new BigInteger(((IntegerLiteral) expr).getValue());
				if (((CPrimitive) cType).isUnsigned()) {
					BigInteger maxValue = m_TypeSizes.getMaxValueOfPrimitiveType((CPrimitive) cType);
					BigInteger maxValuePlusOne = maxValue.add(BigInteger.ONE);
					return value.mod(maxValuePlusOne);
				} else {
					return value;
				}
			} else {
				return null;
			}
		} else {
			return null;
		}
	}
	
	@Override
	public CPrimitive getCTypeOfPointerComponents() {
		return new CPrimitive(PRIMITIVE.LONG);
	}

	@Override
	public void addAssumeValueInRangeStatements(ILocation loc, Expression expr, CType cType, List<Statement> stmt) {
		if (m_AssumeThatSignedValuesAreInRange) {
			if (cType.getUnderlyingType().isIntegerType()) {
				CPrimitive cPrimitive = (CPrimitive) CEnum.replaceEnumWithInt(cType);
				if (!cPrimitive.isUnsigned()) {
					stmt.add(constructAssumeInRangeStatement(m_TypeSizes, loc, expr, cPrimitive));
				}
			}
		}
	}
	
	/**
	 * Returns "assume (minValue <= lrValue && lrValue <= maxValue)"
	 */
	private AssumeStatement constructAssumeInRangeStatement(TypeSizes typeSizes, 
			ILocation loc, Expression expr, CPrimitive type) {
		Expression minValue = constructLiteralForIntegerType(loc, type, typeSizes.getMinValueOfPrimitiveType(type)); 
		Expression maxValue = constructLiteralForIntegerType(loc, type, typeSizes.getMaxValueOfPrimitiveType(type));
				
		Expression biggerMinInt = constructBinaryComparisonExpression(
				loc, IASTBinaryExpression.op_lessEqual, minValue, type, expr, type);
		Expression smallerMaxValue = constructBinaryComparisonExpression(
				loc, IASTBinaryExpression.op_lessEqual, expr, type, maxValue, type); 
		AssumeStatement inRange = new AssumeStatement(loc, ExpressionFactory.newBinaryExpression(loc, 
				BinaryExpression.Operator.LOGICAND, biggerMinInt, smallerMaxValue));
		return inRange;
	}

	@Override
	public Expression extractBits(ILocation loc, Expression operand, int high, int low) {
		// we probably also have to provide information if input is signed/unsigned
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public Expression concatBits(ILocation loc, List<Expression> dataChunks, int size) {
		// we probably also have to provide information if input is signed/unsigned
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public Expression signExtend(ILocation loc, Expression operand, int bitsBefore, int bitsAfter) {
		// we probably also have to provide information if input is signed/unsigned
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public Expression constructBinaryComparisonFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp1,
			CPrimitive type1, Expression exp2, CPrimitive type2) {
		String functionName = "someBinary" + type1.toString() +"ComparisonOperation";
		String prefixedFunctionName = "~" + functionName;
		if (!m_FunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			Attribute[] attributes = new Attribute[] { attribute };
			ASTType paramAstType = m_TypeHandler.ctype2asttype(loc, type1);
			ASTType resultAstType = new PrimitiveType(loc, SFO.BOOL);
			m_FunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultAstType, paramAstType, paramAstType);
		}
		return new FunctionApplication(loc, prefixedFunctionName, new Expression[] { exp1, exp2});
	}

	@Override
	public Expression constructUnaryFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp,
			CPrimitive type) {
		String functionName = "someUnary" + type.toString() +"operation";
		String prefixedFunctionName = "~" + functionName;
		if (!m_FunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			Attribute[] attributes = new Attribute[] { attribute };
			ASTType astType = m_TypeHandler.ctype2asttype(loc, type);
			m_FunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType, astType);
		}
		return new FunctionApplication(loc, prefixedFunctionName, new Expression[] { exp});
	}

	@Override
	public Expression constructArithmeticFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp1,
			CPrimitive type1, Expression exp2, CPrimitive type2) {
		String functionName = "someBinaryArithmetic" + type1.toString() +"operation";
		String prefixedFunctionName = "~" + functionName;
		if (!m_FunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.s_OVERAPPROX_IDENTIFIER, new Expression[] { new StringLiteral(loc, functionName ) });
			Attribute[] attributes = new Attribute[] { attribute };
			ASTType astType = m_TypeHandler.ctype2asttype(loc, type1);
			m_FunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType, astType, astType);
		}
		return new FunctionApplication(loc, prefixedFunctionName, new Expression[] { exp1, exp2});
	}

	@Override
	public Expression constructBinaryEqualityExpression_Floating(ILocation loc, int nodeOperator, Expression exp1,
			CType type1, Expression exp2, CType type2) {
		String prefixedFunctionName = declareBinaryFloatComparisonOperation(loc, (CPrimitive) type1);
		return new FunctionApplication(loc, prefixedFunctionName, new Expression[] { exp1, exp2} );
	}

	@Override
	public Expression constructBinaryEqualityExpression_Integer(ILocation loc, int nodeOperator, Expression exp1,
			CType type1, Expression exp2, CType type2) {
		if ((type1 instanceof CPrimitive) && (type2 instanceof CPrimitive)) {
			CPrimitive primitive1 = (CPrimitive) type1;
			CPrimitive primitive2 = (CPrimitive) type2;
			if (m_UnsignedTreatment == UNSIGNED_TREATMENT.WRAPAROUND && primitive1.isUnsigned()) {
				assert primitive2.isUnsigned();
				exp1 = applyWraparound(loc, m_TypeSizes, primitive1, exp1);
				exp2 = applyWraparound(loc, m_TypeSizes, primitive2, exp2);
			}
		}
		
		if (nodeOperator == IASTBinaryExpression.op_equals) {
			return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, exp1, exp2);
		} else 	if (nodeOperator == IASTBinaryExpression.op_notequals) {
			return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, exp1, exp2);
		} else {
			throw new IllegalArgumentException("operator is neither equals nor not equals");
		}
	}

	@Override
	protected String declareConversionFunction(ILocation loc, CPrimitive oldType, CPrimitive newType) {
		return declareConversionFunctionOverApprox(loc, oldType, newType);
	}
}
