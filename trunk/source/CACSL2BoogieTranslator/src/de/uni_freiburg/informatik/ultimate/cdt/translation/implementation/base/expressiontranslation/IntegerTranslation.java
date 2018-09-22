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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationState;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UnsignedTreatment;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Thomas Lang
 *
 */
public class IntegerTranslation extends ExpressionTranslation {

	private static final boolean OVERAPPROXIMATE_INT_POINTER_CONVERSION = true;

	private final UnsignedTreatment mUnsignedTreatment;

	/**
	 * Add assume statements that state that values of signed integer types are in range.
	 */
	private final boolean mAssumeThatSignedValuesAreInRange;

	public IntegerTranslation(final TypeSizes typeSizeConstants, final CTranslationState handlerHandler,
			final UnsignedTreatment unsignedTreatment, final boolean assumeSignedInRange,
			final PointerIntegerConversion pointerIntegerConversion,
			final boolean overapproximateFloatingPointOperations) {
		super(typeSizeConstants, handlerHandler, pointerIntegerConversion, overapproximateFloatingPointOperations);
		mUnsignedTreatment = unsignedTreatment;
		mAssumeThatSignedValuesAreInRange = assumeSignedInRange;
	}

	@Override
	public RValue translateIntegerLiteral(final ILocation loc, final String val) {
		final RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, false, mTypeSizes);
		return rVal;
	}

	@Override
	public Expression constructLiteralForIntegerType(final ILocation loc, final CPrimitive type,
			final BigInteger value) {
		return ISOIEC9899TC3.constructLiteralForCIntegerLiteral(loc, false, mTypeSizes, type, value);
	}

	@Override
	public Expression constructLiteralForFloatingType(final ILocation loc, final CPrimitive type,
			final BigDecimal value) {
		return ExpressionFactory.createRealLiteral(loc, value.toString());
	}

	@Override
	public Expression constructBinaryComparisonIntegerExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		if (!type1.equals(type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " and " + type2);
		}
		Expression leftExpr = exp1;
		Expression rightExpr = exp2;
		if (mUnsignedTreatment == UnsignedTreatment.WRAPAROUND && mTypeSizes.isUnsigned(type1)) {
			assert mTypeSizes.isUnsigned(type2);
			leftExpr = applyWraparound(loc, mTypeSizes, type1, leftExpr);
			rightExpr = applyWraparound(loc, mTypeSizes, type2, rightExpr);
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
			throw new AssertionError("Unknown BinaryExpression operator " + nodeOperator);
		}

		return ExpressionFactory.newBinaryExpression(loc, op, leftExpr, rightExpr);
	}

	public static Expression applyWraparound(final ILocation loc, final TypeSizes typeSizes,
			final CPrimitive cPrimitive, final Expression operand) {
		if (cPrimitive.getGeneralType() == CPrimitiveCategory.INTTYPE) {
			if (typeSizes.isUnsigned(cPrimitive)) {
				final BigInteger maxValuePlusOne = typeSizes.getMaxValueOfPrimitiveType(cPrimitive).add(BigInteger.ONE);
				return applyEucledeanModulo(loc, operand, maxValuePlusOne);
			}
			throw new AssertionError("wraparound only for unsigned types");
		}
		throw new AssertionError("wraparound only for integer types");
	}

	private static Expression applyEucledeanModulo(final ILocation loc, final Expression operand,
			final BigInteger divisor) {
		return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMOD, operand,
				ExpressionFactory.createIntegerLiteral(loc, divisor.toString()));
	}

	@Override
	public Expression constructBinaryBitwiseIntegerExpression(final ILocation loc, final int op, final Expression left,
			final CPrimitive typeLeft, final Expression right, final CPrimitive typeRight, final IASTNode hook) {
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
		case IASTBinaryExpression.op_shiftLeftAssign: {
			final BigInteger integerLiteralValue = extractIntegerValue(right, typeRight, hook);
			if (integerLiteralValue != null) {
				return constructShiftWithLiteralOptimization(loc, left, typeRight, integerLiteralValue,
						Operator.ARITHMUL);
			}
		}
			funcname = "shiftLeft";
			break;
		case IASTBinaryExpression.op_shiftRight:
		case IASTBinaryExpression.op_shiftRightAssign: {
			final BigInteger integerLiteralValue = extractIntegerValue(right, typeRight, hook);
			if (integerLiteralValue != null) {
				return constructShiftWithLiteralOptimization(loc, left, typeRight, integerLiteralValue,
						Operator.ARITHDIV);
			}
		}
			funcname = "shiftRight";
			break;
		default:
			final String msg = "Unknown or unsupported bitwise expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
		declareBitvectorFunction(loc, prefixedFunctionName, false, typeLeft, typeLeft, typeRight);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { left, right },
				mHandlerHandler.getBoogieTypeHelper().getBoogieTypeForCType(typeLeft));
		return func;
	}

	private Expression constructShiftWithLiteralOptimization(final ILocation loc, final Expression left,
			final CPrimitive typeRight, final BigInteger integerLiteralValue, final Operator op1) {
		// 2017-11-18 Matthias: this could be done analogously in the
		// bitprecise translation
		int exponent;
		try {
			exponent = integerLiteralValue.intValueExact();
		} catch (final ArithmeticException ae) {
			throw new UnsupportedOperationException("rhs of leftshift is larger than C standard allows " + ae);
		}
		final BigInteger shiftFactorBigInt = BigInteger.valueOf(2).pow(exponent);
		final Expression shiftFactorExpr = constructLiteralForIntegerType(loc, typeRight, shiftFactorBigInt);
		final Expression result = ExpressionFactory.newBinaryExpression(loc, op1, left, shiftFactorExpr);
		return result;
	}

	@Override
	public Expression constructUnaryIntegerExpression(final ILocation loc, final int op, final Expression expr,
			final CPrimitive type) {
		switch (op) {
		case IASTUnaryExpression.op_tilde:
			return constructUnaryIntExprTilde(loc, expr, type);
		case IASTUnaryExpression.op_minus:
			return constructUnaryIntExprMinus(loc, expr, type);
		default:
			final String msg = "Unknown or unsupported bitwise expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	private Expression constructUnaryIntExprTilde(final ILocation loc, final Expression expr, final CPrimitive type) {
		final String funcname = "bitwiseComplement";
		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
		declareBitvectorFunction(loc, prefixedFunctionName, false, type, type);
		return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName, new Expression[] { expr },
				mHandlerHandler.getBoogieTypeHelper().getBoogieTypeForCType(type));
	}

	private static Expression constructUnaryIntExprMinus(final ILocation loc, final Expression expr,
			final CPrimitive type) {
		if (type.getGeneralType() == CPrimitiveCategory.INTTYPE) {
			return ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.ARITHNEGATIVE, expr);
		} else if (type.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			// TODO: having boogie deal with negative real literals would be the nice
			// solution..
			return ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMINUS,
					ExpressionFactory.createRealLiteral(loc, "0.0"), expr);
		} else {
			throw new IllegalArgumentException("Unsupported type for unary minus: " + type);
		}
	}

	private void declareBitvectorFunction(final ILocation loc, final String prefixedFunctionName,
			final boolean boogieResultTypeBool, final CPrimitive resultCType, final CPrimitive... paramCType) {
		final String functionName = prefixedFunctionName.substring(1, prefixedFunctionName.length());
		final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
				new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
		final Attribute[] attributes = new Attribute[] { attribute };
		mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + functionName, attributes,
				boogieResultTypeBool, resultCType, paramCType);
	}

	@Override
	public Expression constructArithmeticIntegerExpression(final ILocation loc, final int nodeOperator,
			final Expression leftExp, final CPrimitive leftType, final Expression rightExp,
			final CPrimitive rightType) {
		assert leftType.getGeneralType() == CPrimitiveCategory.INTTYPE;
		assert rightType.getGeneralType() == CPrimitiveCategory.INTTYPE;

		Expression leftExpr = leftExp;
		Expression rightExpr = rightExp;
		if (leftType.isIntegerType() && mTypeSizes.isUnsigned(leftType)) {
			assert rightType.isIntegerType() && mTypeSizes.isUnsigned(rightType) : "incompatible types";
			if (nodeOperator == IASTBinaryExpression.op_divide || nodeOperator == IASTBinaryExpression.op_divideAssign
					|| nodeOperator == IASTBinaryExpression.op_modulo
					|| nodeOperator == IASTBinaryExpression.op_moduloAssign) {
				// apply wraparound to ensure that Nutz transformation is sound
				// (see examples/programs/regression/c/NutzTransformation02.c)
				leftExpr = applyWraparound(loc, mTypeSizes, leftType, leftExpr);
				rightExpr = applyWraparound(loc, mTypeSizes, rightType, rightExpr);
			}
		}
		final boolean bothAreIntegerLiterals =
				leftExpr instanceof IntegerLiteral && rightExpr instanceof IntegerLiteral;
		BigInteger leftValue = null;
		BigInteger rightValue = null;
		// TODO: add checks for UnaryExpression (otherwise we don't catch negative
		// constants, here) --> or remove all
		// the cases
		// (if-then-else conditions are checked for being constant in RCFGBuilder
		// anyway, so this is merely a decision
		// of readability of Boogie code..)
		if (leftExpr instanceof IntegerLiteral) {
			leftValue = new BigInteger(((IntegerLiteral) leftExpr).getValue());
		}
		if (rightExpr instanceof IntegerLiteral) {
			rightValue = new BigInteger(((IntegerLiteral) rightExpr).getValue());
		}
		switch (nodeOperator) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			return constructArithmeticExpression(loc, nodeOperator, leftExp, rightExp);
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide:
			return constructArIntExprDiv(loc, leftExpr, rightExpr, bothAreIntegerLiterals, leftValue, rightValue);
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
			return constructArIntExprMod(loc, leftExpr, rightExpr, bothAreIntegerLiterals, leftValue, rightValue);
		default:
			final String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	private static Expression constructArIntExprDiv(final ILocation loc, final Expression exp1, final Expression exp2,
			final boolean bothAreIntegerLiterals, final BigInteger leftValue, final BigInteger rightValue) {
		final BinaryExpression.Operator operator;
		operator = Operator.ARITHDIV;
		/*
		 * In C the semantics of integer division is "rounding towards zero". In Boogie euclidian division is used. We
		 * translate a / b into (a < 0 && a%b != 0) ? ( (b < 0) ? (a/b)+1 : (a/b)-1) : a/b
		 */
		if (bothAreIntegerLiterals) {
			final String constantResult = leftValue.divide(rightValue).toString();
			return ExpressionFactory.createIntegerLiteral(loc, constantResult);
		}
		final Expression leftSmallerZeroAndThereIsRemainder = getLeftSmallerZeroAndThereIsRemainder(loc, exp1, exp2);
		final Expression rightSmallerZero = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
				exp2, ExpressionFactory.createIntegerLiteral(loc, SFO.NR0));
		final Expression normalDivision = ExpressionFactory.newBinaryExpression(loc, operator, exp1, exp2);
		if (exp1 instanceof IntegerLiteral) {
			if (leftValue.signum() == 1) {
				return normalDivision;
			} else if (leftValue.signum() == -1) {
				return ExpressionFactory.constructIfThenElseExpression(loc, rightSmallerZero,
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMINUS, normalDivision,
								ExpressionFactory.createIntegerLiteral(loc, SFO.NR1)),
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS, normalDivision,
								ExpressionFactory.createIntegerLiteral(loc, SFO.NR1)));
			} else {
				return ExpressionFactory.createIntegerLiteral(loc, SFO.NR0);
			}
		} else if (exp2 instanceof IntegerLiteral) {
			if (rightValue.signum() == 1 || rightValue.signum() == 0) {
				return ExpressionFactory
						.constructIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder,
								ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS,
										normalDivision, ExpressionFactory.createIntegerLiteral(loc, SFO.NR1)),
								normalDivision);
			} else if (rightValue.signum() == -1) {
				return ExpressionFactory
						.constructIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder,
								ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMINUS,
										normalDivision, ExpressionFactory.createIntegerLiteral(loc, SFO.NR1)),
								normalDivision);
			}
			throw new UnsupportedOperationException("Is it expected that this is a fall-through switch?");
		} else {
			return ExpressionFactory.constructIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder,
					ExpressionFactory.constructIfThenElseExpression(loc, rightSmallerZero,
							ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMINUS,
									normalDivision, ExpressionFactory.createIntegerLiteral(loc, SFO.NR1)),
							ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS,
									normalDivision, ExpressionFactory.createIntegerLiteral(loc, SFO.NR1))),
					normalDivision);
		}
	}

	private static Expression constructArIntExprMod(final ILocation loc, final Expression exp1, final Expression exp2,
			final boolean bothAreIntegerLiterals, final BigInteger leftValue, final BigInteger rightValue) {
		final BinaryExpression.Operator operator;
		operator = Operator.ARITHMOD;
		/*
		 * In C the semantics of integer division is "rounding towards zero". In Boogie euclidian division is used. We
		 * translate a % b into (a < 0 && a%b != 0) ? ( (b < 0) ? (a%b)-b : (a%b)+b) : a%b
		 */
		// modulo on bigInteger does not seem to follow the "multiply, add, and get the
		// result back"-rule, together
		// with its division..
		if (bothAreIntegerLiterals) {
			final String constantResult;
			if (leftValue.signum() == 1 || leftValue.signum() == 0) {
				if (rightValue.signum() == 1) {
					constantResult = leftValue.mod(rightValue).toString();
				} else if (rightValue.signum() == -1) {
					constantResult = leftValue.mod(rightValue.negate()).toString();
				} else {
					constantResult = "0";
				}
			} else if (leftValue.signum() == -1) {
				if (rightValue.signum() == 1) {
					constantResult = (leftValue.negate().mod(rightValue)).negate().toString();
				} else if (rightValue.signum() == -1) {
					constantResult = (leftValue.negate().mod(rightValue.negate())).negate().toString();
				} else {
					constantResult = "0";
				}
			} else {
				throw new UnsupportedOperationException("constant is not assigned");
			}
			return ExpressionFactory.createIntegerLiteral(loc, constantResult);
		}
		final Expression leftSmallerZeroAndThereIsRemainder = getLeftSmallerZeroAndThereIsRemainder(loc, exp1, exp2);
		final Expression rightSmallerZero = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
				exp2, ExpressionFactory.createIntegerLiteral(loc, SFO.NR0));
		final Expression normalModulo = ExpressionFactory.newBinaryExpression(loc, operator, exp1, exp2);
		if (exp1 instanceof IntegerLiteral) {
			if (leftValue.signum() == 1) {
				return normalModulo;
			} else if (leftValue.signum() == -1) {
				return ExpressionFactory.constructIfThenElseExpression(loc, rightSmallerZero,
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS, normalModulo,
								exp2),
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMINUS, normalModulo,
								exp2));
			} else {
				return ExpressionFactory.createIntegerLiteral(loc, SFO.NR0);
			}
		} else if (exp2 instanceof IntegerLiteral) {
			if (rightValue.signum() == 1 || rightValue.signum() == 0) {
				return ExpressionFactory.constructIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder,
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMINUS, normalModulo,
								exp2),
						normalModulo);
			} else if (rightValue.signum() == -1) {
				return ExpressionFactory.constructIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder,
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS, normalModulo,
								exp2),
						normalModulo);
			}
			throw new UnsupportedOperationException("Is it expected that this is a fall-through switch?");
		} else {
			return ExpressionFactory.constructIfThenElseExpression(loc, leftSmallerZeroAndThereIsRemainder,
					ExpressionFactory.constructIfThenElseExpression(loc, rightSmallerZero,
							ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHPLUS,
									normalModulo, exp2),
							ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMINUS,
									normalModulo, exp2)),
					normalModulo);
		}
	}

	private static Expression getLeftSmallerZeroAndThereIsRemainder(final ILocation loc, final Expression exp1,
			final Expression exp2) {
		final Expression leftModRight = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMOD, exp1, exp2);
		final Expression thereIsRemainder = ExpressionFactory.newBinaryExpression(loc, Operator.COMPNEQ, leftModRight,
				ExpressionFactory.createIntegerLiteral(loc, SFO.NR0));
		final Expression leftSmallerZero = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
				exp1, ExpressionFactory.createIntegerLiteral(loc, SFO.NR0));
		return ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftSmallerZero, thereIsRemainder);
	}

	@Override
	public void convertIntToInt_NonBool(final ILocation loc, final ExpressionResult operand,
			final CPrimitive resultType) {
		if (resultType.isIntegerType()) {
			convertToIntegerType(loc, operand, resultType);
		} else {
			throw new UnsupportedOperationException("not yet supported: conversion to " + resultType);
		}
	}

	private void convertToIntegerType(final ILocation loc, final ExpressionResult operand,
			final CPrimitive resultType) {
		assert resultType.isIntegerType();
		final CPrimitive oldType = (CPrimitive) operand.getLrValue().getCType().getUnderlyingType();
		if (oldType.isIntegerType()) {
			final Expression newExpression;
			if (mTypeSizes.isUnsigned(resultType)) {
				final Expression oldWrappedIfNeeded;
				if (mTypeSizes.isUnsigned(oldType)
						&& mTypeSizes.getSize(resultType.getType()) > mTypeSizes.getSize(oldType.getType())) {
					// required for sound Nutz transformation
					// (see examples/programs/regression/c/NutzTransformation03.c)
					oldWrappedIfNeeded = applyWraparound(loc, mTypeSizes, oldType, operand.getLrValue().getValue());
				} else {
					oldWrappedIfNeeded = operand.getLrValue().getValue();
				}
				if (mUnsignedTreatment == UnsignedTreatment.ASSERT) {
					final BigInteger maxValuePlusOne =
							mTypeSizes.getMaxValueOfPrimitiveType(resultType).add(BigInteger.ONE);
					final AssertStatement assertGeq0 = new AssertStatement(loc,
							ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
									oldWrappedIfNeeded, ExpressionFactory.createIntegerLiteral(loc, SFO.NR0)));
					final Check chk1 = new Check(Spec.UINT_OVERFLOW);
					chk1.annotate(assertGeq0);
					operand.mStmt.add(assertGeq0);

					final AssertStatement assertLtMax = new AssertStatement(loc,
							ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
									oldWrappedIfNeeded,
									ExpressionFactory.createIntegerLiteral(loc, maxValuePlusOne.toString())));
					final Check chk2 = new Check(Spec.UINT_OVERFLOW);
					chk2.annotate(assertLtMax);
					operand.mStmt.add(assertLtMax);
				} else {
					// do nothing
				}
				newExpression = oldWrappedIfNeeded;
			} else {
				assert !mTypeSizes.isUnsigned(resultType);
				final Expression oldWrappedIfUnsigned;
				if (mTypeSizes.isUnsigned(oldType)) {
					// required for sound Nutz transformation
					// (see examples/programs/regression/c/NutzTransformation01.c)
					oldWrappedIfUnsigned = applyWraparound(loc, mTypeSizes, oldType, operand.getLrValue().getValue());
				} else {
					oldWrappedIfUnsigned = operand.getLrValue().getValue();
				}
				if (mTypeSizes.getSize(resultType.getType()) > mTypeSizes.getSize(oldType.getType())
						|| (mTypeSizes.getSize(resultType.getType()).equals(mTypeSizes.getSize(oldType.getType()))
								&& !mTypeSizes.isUnsigned(oldType))) {
					newExpression = oldWrappedIfUnsigned;
				} else {
					// According to C11 6.3.1.3.3 the result is implementation-defined
					// it the value cannot be represented by the new type
					// We have chosen an implementation that is similar to
					// taking the lowest bits in a two's complement representation:
					// First we take the value modulo the cardinality of the
					// data range (which is 2*(MAX_VALUE+1) for signed )
					// If the number is strictly larger than MAX_VALUE we
					// subtract the cardinality of the data range.
					final CPrimitive correspondingUnsignedType = mTypeSizes.getCorrespondingUnsignedType(resultType);
					final Expression wrapped =
							applyWraparound(loc, mTypeSizes, correspondingUnsignedType, oldWrappedIfUnsigned);
					final Expression maxValue = constructLiteralForIntegerType(loc, oldType,
							mTypeSizes.getMaxValueOfPrimitiveType(resultType));
					final Expression condition =
							ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, wrapped, maxValue);
					final Expression range = constructLiteralForIntegerType(loc, oldType,
							mTypeSizes.getMaxValueOfPrimitiveType(correspondingUnsignedType).add(BigInteger.ONE));
					newExpression = ExpressionFactory.constructIfThenElseExpression(loc, condition, wrapped,
							ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMINUS, wrapped, range));
				}

			}
			final RValue newRValue = new RValue(newExpression, resultType, false, false);
			operand.setLrValue(newRValue);
		} else {
			throw new UnsupportedOperationException("not yet supported: conversion from " + oldType);
		}
	}

	public void oldConvertPointerToInt(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		assert newType.isIntegerType();
		assert rexp.getLrValue().getCType().getUnderlyingType() instanceof CPointer;
		if (OVERAPPROXIMATE_INT_POINTER_CONVERSION) {
			super.convertPointerToInt(loc, rexp, newType);
		} else {
			final Expression pointerExpression = rexp.getLrValue().getValue();
			final Expression intExpression;
			if (mTypeSizes.useFixedTypeSizes()) {
				final BigInteger maxPtrValuePlusOne = mTypeSizes.getMaxValueOfPointer().add(BigInteger.ONE);
				final IntegerLiteral maxPointer =
						ExpressionFactory.createIntegerLiteral(loc, maxPtrValuePlusOne.toString());
				intExpression = constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
						constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
								MemoryHandler.getPointerBaseAddress(pointerExpression, loc), newType, maxPointer,
								newType),
						newType, MemoryHandler.getPointerOffset(pointerExpression, loc), newType);
			} else {
				intExpression = MemoryHandler.getPointerOffset(pointerExpression, loc);
			}
			final RValue rValue = new RValue(intExpression, newType, false, true);
			rexp.setLrValue(rValue);
		}
	}

	public void oldConvertIntToPointer(final ILocation loc, final ExpressionResult rexp, final CPointer newType) {
		if (OVERAPPROXIMATE_INT_POINTER_CONVERSION) {
			super.convertIntToPointer(loc, rexp, newType);
		} else {
			final Expression intExpression = rexp.getLrValue().getValue();
			final Expression baseAdress;
			final Expression offsetAdress;
			if (mTypeSizes.useFixedTypeSizes()) {
				final BigInteger maxPtrValuePlusOne = mTypeSizes.getMaxValueOfPointer().add(BigInteger.ONE);
				final IntegerLiteral maxPointer =
						ExpressionFactory.createIntegerLiteral(loc, maxPtrValuePlusOne.toString());
				baseAdress = constructArithmeticExpression(loc, IASTBinaryExpression.op_divide, intExpression,
						getCTypeOfPointerComponents(), maxPointer, getCTypeOfPointerComponents());
				offsetAdress = constructArithmeticExpression(loc, IASTBinaryExpression.op_modulo, intExpression,
						getCTypeOfPointerComponents(), maxPointer, getCTypeOfPointerComponents());
			} else {
				baseAdress = constructLiteralForIntegerType(loc, getCTypeOfPointerComponents(), BigInteger.ZERO);
				offsetAdress = intExpression;
			}
			final Expression pointerExpression =
					MemoryHandler.constructPointerFromBaseAndOffset(baseAdress, offsetAdress, loc);
			final RValue rValue = new RValue(pointerExpression, newType, false, false);
			rexp.setLrValue(rValue);
		}
	}

	@Override
	public BigInteger extractIntegerValue(final Expression expr, final CType cType, final IASTNode hook) {
		if (cType.isIntegerType()) {
			if (expr instanceof IntegerLiteral) {
				final BigInteger value = new BigInteger(((IntegerLiteral) expr).getValue());
				if (mTypeSizes.isUnsigned(((CPrimitive) cType))) {
					final BigInteger maxValue = mTypeSizes.getMaxValueOfPrimitiveType((CPrimitive) cType);
					final BigInteger maxValuePlusOne = maxValue.add(BigInteger.ONE);
					return value.mod(maxValuePlusOne);
				}
				return value;
			} else if (expr instanceof IdentifierExpression) {
				// An IdentifierExpression may be an alias for an integer value, this is stored in the symbol table.
				final String bId = ((IdentifierExpression) expr).getIdentifier();
				final String cId = mTypeHandler.getCHandler().getSymbolTable().getCIdForBoogieId(bId);
				final SymbolTableValue stv = mTypeHandler.getCHandler().getSymbolTable().findCSymbol(hook, cId);
				if (stv.hasConstantValue()) {
					return extractIntegerValue(stv.getConstantValue(), cType, hook);
				}
			}
			return null;
		}
		return null;
	}

	@Override
	public CPrimitive getCTypeOfPointerComponents() {
		return new CPrimitive(CPrimitives.LONG);
	}

	@Override
	public void addAssumeValueInRangeStatements(final ILocation loc, final Expression expr, final CType cType,
			final List<Statement> stmt) {
		if (mAssumeThatSignedValuesAreInRange && cType.getUnderlyingType().isIntegerType()) {
			final CPrimitive cPrimitive = (CPrimitive) CEnum.replaceEnumWithInt(cType);
			if (!mTypeSizes.isUnsigned(cPrimitive)) {
				stmt.add(constructAssumeInRangeStatement(mTypeSizes, loc, expr, cPrimitive));
			}
		}
	}

	@Override
	public void addAssumeValueInRangeStatements(final ILocation loc, final Expression expr, final CType cType,
			final ExpressionResultBuilder expressionResultBuilder) {
		if (mAssumeThatSignedValuesAreInRange && cType.getUnderlyingType().isIntegerType()) {
			final CPrimitive cPrimitive = (CPrimitive) CEnum.replaceEnumWithInt(cType.getUnderlyingType());
			if (!mTypeSizes.isUnsigned(cPrimitive)) {
				expressionResultBuilder
						.addStatement(constructAssumeInRangeStatement(mTypeSizes, loc, expr, cPrimitive));
			}
		}
	}

	/**
	 * Returns "assume (minValue <= lrValue && lrValue <= maxValue)"
	 */
	private AssumeStatement constructAssumeInRangeStatement(final TypeSizes typeSizes, final ILocation loc,
			final Expression expr, final CPrimitive type) {
		final Expression minValue =
				constructLiteralForIntegerType(loc, type, typeSizes.getMinValueOfPrimitiveType(type));
		final Expression maxValue =
				constructLiteralForIntegerType(loc, type, typeSizes.getMaxValueOfPrimitiveType(type));

		final Expression biggerMinInt =
				constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, minValue, type, expr, type);
		final Expression smallerMaxValue =
				constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, expr, type, maxValue, type);
		final AssumeStatement inRange = new AssumeStatement(loc, ExpressionFactory.newBinaryExpression(loc,
				BinaryExpression.Operator.LOGICAND, biggerMinInt, smallerMaxValue));
		return inRange;
	}

	@Override
	public Expression extractBits(final ILocation loc, final Expression operand, final int high, final int low) {
		// we probably also have to provide information if input is signed/unsigned
		throw new UnsupportedOperationException("not yet implemented in non-bitprecise translation");
	}

	@Override
	public Expression concatBits(final ILocation loc, final List<Expression> dataChunks, final int size) {
		// we probably also have to provide information if input is signed/unsigned
		throw new UnsupportedOperationException("not yet implemented in non-bitprecise translation");
	}

	@Override
	public Expression signExtend(final ILocation loc, final Expression operand, final int bitsBefore,
			final int bitsAfter) {
		// we probably also have to provide information if input is signed/unsigned
		throw new UnsupportedOperationException("not yet implemented in non-bitprecise translation");
	}

	@Override
	public Expression constructBinaryComparisonFloatingPointExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		if (mOverapproximateFloatingPointOperations) {
			final String functionName = "someBinary" + type1.toString() + "ComparisonOperation";
			final String prefixedFunctionName = "~" + functionName;
			if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
				final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
						new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
				final Attribute[] attributes = new Attribute[] { attribute };
				final ASTType paramAstType = mTypeHandler.cType2AstType(loc, type1);
				final ASTType resultAstType = new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL);
				mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultAstType,
						paramAstType, paramAstType);
			}
			return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
					new Expression[] { exp1, exp2 }, BoogieType.TYPE_BOOL);
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
			throw new AssertionError("Unknown BinaryExpression operator " + nodeOperator);
		}

		return ExpressionFactory.newBinaryExpression(loc, op, exp1, exp2);
	}

	@Override
	public Expression constructUnaryFloatingPointExpression(final ILocation loc, final int nodeOperator,
			final Expression exp, final CPrimitive type) {
		if (mOverapproximateFloatingPointOperations) {
			final String functionName = "someUnary" + type.toString() + "operation";
			final String prefixedFunctionName = "~" + functionName;
			if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
				final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
						new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
				final Attribute[] attributes = new Attribute[] { attribute };
				final ASTType astType = mTypeHandler.cType2AstType(loc, type);
				mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType, astType);
			}
			return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName, new Expression[] { exp },
					mHandlerHandler.getBoogieTypeHelper().getBoogieTypeForCType(type));
		}
		return constructUnaryIntExprMinus(loc, exp, type);
	}

	@Override
	public Expression constructArithmeticFloatingPointExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		if (mOverapproximateFloatingPointOperations) {
			final String functionName = "someBinaryArithmetic" + type1.toString() + "operation";
			final String prefixedFunctionName = "~" + functionName;
			if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
				final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
						new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
				final Attribute[] attributes = new Attribute[] { attribute };
				final ASTType astType = mTypeHandler.cType2AstType(loc, type1);
				mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType, astType, astType);
			}
			return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
					new Expression[] { exp1, exp2 },
					mHandlerHandler.getBoogieTypeHelper().getBoogieTypeForCType(type1));
		}
		return constructArithmeticExpression(loc, nodeOperator, exp1, exp2);
	}

	private static Expression constructArithmeticExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final Expression exp2) {
		final BinaryExpression.Operator operator;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
			operator = Operator.ARITHMINUS;
			break;
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
			operator = Operator.ARITHMUL;
			break;
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide:
			operator = Operator.ARITHDIV;
			break;
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
			operator = Operator.ARITHMOD;
			break;
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			operator = Operator.ARITHPLUS;
			break;
		default:
			final String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		return ExpressionFactory.newBinaryExpression(loc, operator, exp1, exp2);
	}

	@Override
	public Expression constructBinaryEqualityExpressionFloating(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CType type1, final Expression exp2, final CType type2) {
		final String prefixedFunctionName = declareBinaryFloatComparisonOverApprox(loc, (CPrimitive) type1);
		if (mOverapproximateFloatingPointOperations) {
			return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
					new Expression[] { exp1, exp2 }, BoogieType.TYPE_BOOL);
		}
		return constructEquality(loc, nodeOperator, exp1, exp2);
	}

	@Override
	public Expression constructBinaryEqualityExpressionInteger(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CType type1, final Expression exp2, final CType type2) {
		Expression leftExpr = exp1;
		Expression rightExpr = exp2;
		if ((type1 instanceof CPrimitive) && (type2 instanceof CPrimitive)) {
			final CPrimitive primitive1 = (CPrimitive) type1;
			final CPrimitive primitive2 = (CPrimitive) type2;
			if (mUnsignedTreatment == UnsignedTreatment.WRAPAROUND && mTypeSizes.isUnsigned(primitive1)) {
				assert mTypeSizes.isUnsigned(primitive2);
				leftExpr = applyWraparound(loc, mTypeSizes, primitive1, leftExpr);
				rightExpr = applyWraparound(loc, mTypeSizes, primitive2, rightExpr);
			}
		}
		return constructEquality(loc, nodeOperator, leftExpr, rightExpr);
	}

	/**
	 * Construct either equals or not-equals relation, depending on nodeOperator.
	 */
	private static Expression constructEquality(final ILocation loc, final int nodeOperator, final Expression leftExpr,
			final Expression rightExpr) {
		if (nodeOperator == IASTBinaryExpression.op_equals) {
			return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, leftExpr, rightExpr);
		} else if (nodeOperator == IASTBinaryExpression.op_notequals) {
			return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, leftExpr, rightExpr);
		} else {
			throw new IllegalArgumentException("operator is neither equals nor not equals");
		}
	}

	// @Override
	// protected String declareConversionFunction(final ILocation loc, final
	// CPrimitive oldType, final CPrimitive
	// newType) {
	// return declareConversionFunctionOverApprox(loc, oldType, newType);
	// }

	@Override
	public ExpressionResult createNanOrInfinity(final ILocation loc, final String name) {
		throw new UnsupportedOperationException("createNanOrInfinity is unsupported in non-bitprecise translation");
	}

	@Override
	public Expression getRoundingMode() {
		throw new UnsupportedOperationException("getRoundingMode is unsupported in non-bitprecise translation");
	}

	@Override
	public RValue constructOtherUnaryFloatOperation(final ILocation loc, final FloatFunction floatFunction,
			final RValue argument) {
		throw new UnsupportedOperationException("floating point operation not supported in non-bitprecise translation: "
				+ floatFunction.getFunctionName());
	}

	@Override
	public RValue constructOtherBinaryFloatOperation(final ILocation loc, final FloatFunction floatFunction,
			final RValue first, final RValue second) {
		throw new UnsupportedOperationException("floating point operation not supported in non-bitprecise translation: "
				+ floatFunction.getFunctionName());
	}

	@Override
	public void convertFloatToFloat(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		final RValue oldRValue = (RValue) rexp.getLrValue();
		rexp.setLrValue(new RValue(oldRValue.getValue(), newType));
	}

	@Override
	public void convertIntToFloat(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		doFloatIntAndIntFloatConversion(loc, rexp, newType);
	}

	@Override
	public void convertFloatToInt_NonBool(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		doFloatIntAndIntFloatConversion(loc, rexp, newType);
	}

	private void doFloatIntAndIntFloatConversion(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		final String prefixedFunctionName =
				declareConversionFunction(loc, (CPrimitive) rexp.getLrValue().getCType().getUnderlyingType(), newType);
		final Expression oldExpression = rexp.getLrValue().getValue();
		final Expression resultExpression = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { oldExpression },
				mHandlerHandler.getBoogieTypeHelper().getBoogieTypeForCType(newType));
		final RValue rValue = new RValue(resultExpression, newType, false, false);
		rexp.setLrValue(rValue);
	}

	@Override
	protected String declareConversionFunction(final ILocation loc, final CPrimitive oldType,
			final CPrimitive newType) {

		final String functionName = "convert" + oldType.toString() + "To" + newType.toString();
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {

			final Attribute[] attributes;
			final ASTType paramASTType = mTypeHandler.cType2AstType(loc, oldType);
			if (newType.isFloatingType()) {
				attributes = generateAttributes(loc, mOverapproximateFloatingPointOperations, "to_real", null);
			} else if (newType.isIntegerType()) {
				attributes = generateAttributes(loc, mOverapproximateFloatingPointOperations, "to_int", null);
			} else {
				throw new AssertionError("unhandled case");
			}
			final ASTType[] params = new ASTType[] { paramASTType };
			final ASTType resultASTType = mTypeHandler.cType2AstType(loc, newType);

			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultASTType, params);
		}
		return prefixedFunctionName;
	}

	@Override
	public Expression transformBitvectorToFloat(final ILocation loc, final Expression bitvector,
			final CPrimitives floatType) {
		throw new UnsupportedOperationException(
				"conversion from bitvector to float not supported in non-bitprecise translation");
	}

	@Override
	public Expression transformFloatToBitvector(final ILocation loc, final Expression value,
			final CPrimitives cprimitive) {
		throw new UnsupportedOperationException(
				"conversion from float to bitvector not supported in non-bitprecise translation");
	}

	@Override
	public Expression eraseBits(final ILocation loc, final Expression value, final CPrimitive cType,
			final int remainingWith, final IASTNode hook) {
		return applyEucledeanModulo(loc, value, BigInteger.valueOf(2).pow(remainingWith));
	}

}
