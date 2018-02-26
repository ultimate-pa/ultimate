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
import java.util.Iterator;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes.FloatingPointSize;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;

public class BitvectorTranslation extends ExpressionTranslation {

	private final Expression mRoundingMode;
	public static final String BOOGIE_ROUNDING_MODE_IDENTIFIER = "FloatRoundingMode";
	public static final String BOOGIE_ROUNDING_MODE_RNE = "RoundingMode_RNE";
	public static final String BOOGIE_ROUNDING_MODE_RTZ = "RoundingMode_RTZ";

	public static final String SMT_LIB_NAN = "NaN";
	public static final String SMT_LIB_PLUS_INF = "+oo";
	public static final String SMT_LIB_MINUS_INF = "-oo";
	public static final String SMT_LIB_PLUS_ZERO = "+zero";
	public static final String SMT_LIB_MINUS_ZERO = "-zero";

	public BitvectorTranslation(final TypeSizes mTypeSizeConstants, final ITypeHandler typeHandler,
			final PointerIntegerConversion pointerIntegerConversion,
			final boolean overapproximateFloatingPointOperations) {
		super(mTypeSizeConstants, typeHandler, pointerIntegerConversion, overapproximateFloatingPointOperations);
		final IdentifierExpression roundingMode = new IdentifierExpression(null, BOOGIE_ROUNDING_MODE_RNE);
		roundingMode.setDeclarationInformation(new DeclarationInformation(StorageClass.GLOBAL, null));
		mRoundingMode = roundingMode;
	}

	@Override
	public RValue translateIntegerLiteral(final ILocation loc, final String val) {
		final RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, true, mTypeSizes);
		return rVal;
	}

	@Override
	public Expression constructLiteralForFloatingType(final ILocation loc, final CPrimitive type,
			final BigDecimal value) {
		if (mOverapproximateFloatingPointOperations) {
			return super.constructOverapproximationFloatLiteral(loc, value.toString(), type);
		}
		final Expression[] arguments;
		final String smtFunctionName;
		if (value.compareTo(BigDecimal.ZERO) == 0) {
			smtFunctionName = SMT_LIB_PLUS_ZERO;
			arguments = new Expression[] {};
		} else {
			smtFunctionName = "to_fp";
			final Expression realValue = new RealLiteral(loc, value.toString());
			arguments = new Expression[] { getRoundingMode(), realValue };
		}
		return new FunctionApplication(loc, SFO.getBoogieFunctionName(smtFunctionName, type), arguments);
	}

	@Override
	public Expression constructLiteralForIntegerType(final ILocation loc, final CPrimitive type,
			final BigInteger value) {
		return ISOIEC9899TC3.constructLiteralForCIntegerLiteral(loc, true, mTypeSizes, type, value);
	}

	@Override
	public Expression constructBinaryComparisonIntegerExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		if (!mFunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}
		final Expression result;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals:
			result = constructBinaryEqualityExpression(loc, nodeOperator, exp1, type1, exp2, type2);
			break;
		case IASTBinaryExpression.op_greaterEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_lessThan:
			result = constructBinaryInequalityExpression(loc, nodeOperator, exp1, type1, exp2, type2);
			break;
		default:
			throw new AssertionError("unknown operation " + nodeOperator);
		}

		return result;
	}

	public Expression constructBinaryInequalityExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		if (!mFunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}
		final String functionName;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_greaterEqual:
			if (mTypeSizes.isUnsigned(type1) && mTypeSizes.isUnsigned(type2)) {
				functionName = "bvuge";
			} else if (!mTypeSizes.isUnsigned(type1) && !mTypeSizes.isUnsigned(type2)) {
				functionName = "bvsge";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		case IASTBinaryExpression.op_greaterThan:
			if (mTypeSizes.isUnsigned(type1) && mTypeSizes.isUnsigned(type2)) {
				functionName = "bvugt";
			} else if (!mTypeSizes.isUnsigned(type1) && !mTypeSizes.isUnsigned(type2)) {
				functionName = "bvsgt";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		case IASTBinaryExpression.op_lessEqual:
			if (mTypeSizes.isUnsigned(type1) && mTypeSizes.isUnsigned(type2)) {
				functionName = "bvule";
			} else if (!mTypeSizes.isUnsigned(type1) && !mTypeSizes.isUnsigned(type2)) {
				functionName = "bvsle";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		case IASTBinaryExpression.op_lessThan:

			if (mTypeSizes.isUnsigned(type1) && mTypeSizes.isUnsigned(type2)) {
				functionName = "bvult";
			} else if (!mTypeSizes.isUnsigned(type1) && !mTypeSizes.isUnsigned(type2)) {
				functionName = "bvslt";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned arguments");
			}
			break;
		default:
			throw new AssertionError("unknown operation " + nodeOperator);
		}
		declareBitvectorFunction(loc, functionName,
				functionName + mFunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), true,
				new CPrimitive(CPrimitives.BOOL), null, type1, type2);
		final Expression result = new FunctionApplication(loc,
				SFO.AUXILIARY_FUNCTION_PREFIX + functionName
						+ mFunctionDeclarations.computeBitvectorSuffix(loc, type1, type2),
				new Expression[] { exp1, exp2 });
		return result;
	}

	@Override
	public Expression constructBinaryBitwiseIntegerExpression(final ILocation loc, final int op, final Expression left,
			final CPrimitive typeLeft, final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		if (!mFunctionDeclarations.checkParameters(typeLeft, typeRight)) {
			throw new IllegalArgumentException("incompatible types " + typeLeft + " " + typeRight);
		}
		final String funcname;
		switch (op) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryAndAssign:
			funcname = "bvand";
			break;
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryOrAssign:
			funcname = "bvor";
			break;
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryXorAssign:
			funcname = "bvxor";
			break;
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftLeftAssign:
			funcname = "bvshl";
			break;
		case IASTBinaryExpression.op_shiftRight:
		case IASTBinaryExpression.op_shiftRightAssign:
			if (mTypeSizes.isUnsigned(typeLeft)) {
				funcname = "bvlshr";
			} else {
				funcname = "bvashr";
			}
			break;
		default:
			final String msg = "Unknown or unsupported bitwise expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		declareBitvectorFunction(loc, funcname,
				funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, typeLeft, typeRight), false, typeLeft,
				null, typeLeft, typeRight);
		final Expression func = new FunctionApplication(loc,
				SFO.AUXILIARY_FUNCTION_PREFIX + funcname
						+ mFunctionDeclarations.computeBitvectorSuffix(loc, typeLeft, typeRight),
				new Expression[] { left, right });
		return func;
	}

	@Override
	public Expression constructUnaryIntegerExpression(final ILocation loc, final int op, final Expression expr,
			final CPrimitive type) {
		final String funcname;
		switch (op) {
		case IASTUnaryExpression.op_tilde:
			funcname = "bvnot";
			break;
		case IASTUnaryExpression.op_minus:
			funcname = "bvneg";
			break;
		default:
			final String msg = "Unknown or unsupported unary expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		declareBitvectorFunction(loc, funcname, funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, type),
				false, type, null, type);
		final Expression func = new FunctionApplication(loc,
				SFO.AUXILIARY_FUNCTION_PREFIX + funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, type),
				new Expression[] { expr });
		return func;
	}

	@Override
	public Expression constructArithmeticIntegerExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		FunctionApplication func;
		if (!mFunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}
		final String funcname;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
			funcname = "bvsub";
			break;
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
			funcname = "bvmul";
			break;
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide:
			if (mTypeSizes.isUnsigned(type1) && mTypeSizes.isUnsigned(type2)) {
				funcname = "bvudiv";
			} else if (!mTypeSizes.isUnsigned(type1) && !mTypeSizes.isUnsigned(type2)) {
				funcname = "bvsdiv";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned");
			}
			break;
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
			if (mTypeSizes.isUnsigned(type1) && mTypeSizes.isUnsigned(type2)) {
				funcname = "bvurem";
			} else if (!mTypeSizes.isUnsigned(type1) && !mTypeSizes.isUnsigned(type2)) {
				funcname = "bvsrem";
			} else {
				throw new IllegalArgumentException("Mixed signed and unsigned");
			}
			break;
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			funcname = "bvadd";
			break;
		default:
			final String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}

		declareBitvectorFunction(loc, funcname,
				funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, type1, type2), false, type1, null, type1,
				type2);
		func = new FunctionApplication(loc,
				SFO.AUXILIARY_FUNCTION_PREFIX + funcname
						+ mFunctionDeclarations.computeBitvectorSuffix(loc, type1, type2),
				new Expression[] { exp1, exp2 });

		return func;
	}

	public void declareBitvectorFunction(final ILocation loc, final String smtFunctionName,
			final String boogieFunctionName, final boolean boogieResultTypeBool, final CPrimitive resultCType,
			final int[] indices, final CPrimitive... paramCType) {
		if (mFunctionDeclarations.getDeclaredFunctions()
				.containsKey(SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName)) {
			// function already declared
			return;
		}
		final Attribute[] attributes = generateAttributes(loc, false, smtFunctionName, indices);
		mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName, attributes,
				boogieResultTypeBool, resultCType, paramCType);
	}

	private void declareFloatingPointFunction(final ILocation loc, final String smtFunctionName,
			final boolean boogieResultTypeBool, final boolean isRounded, final CPrimitive resultCType,
			final int[] indices, final CPrimitive... paramCType) {
		// first parameter defined Boogie function name
		final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, paramCType[0]);
		if (mFunctionDeclarations.getDeclaredFunctions().containsKey(boogieFunctionName)) {
			// function already declared
			return;
		}
		final Attribute[] attributes =
				generateAttributes(loc, mOverapproximateFloatingPointOperations, smtFunctionName, indices);
		if (isRounded) {
			final ASTType[] paramASTTypes = new ASTType[paramCType.length + 1];
			final ASTType resultASTType = mTypeHandler.cType2AstType(loc, resultCType);
			int counter = 1;
			paramASTTypes[0] = new NamedType(loc, BOOGIE_ROUNDING_MODE_IDENTIFIER, new ASTType[0]);
			for (final CPrimitive cType : paramCType) {
				paramASTTypes[counter] = mTypeHandler.cType2AstType(loc, cType);
				counter += 1;
			}
			mFunctionDeclarations.declareFunction(loc, boogieFunctionName, attributes, resultASTType, paramASTTypes);
		} else {
			mFunctionDeclarations.declareFunction(loc, boogieFunctionName, attributes, boogieResultTypeBool,
					resultCType, paramCType);
		}
	}

	public void declareFloatingPointConstructors(final ILocation loc, final CPrimitive type) {
		declareFloatingPointConstructorFromBitvec(loc, type);
		declareFloatingPointConstructorFromReal(loc, type);
	}

	private void declareFloatingPointConstructorFromReal(final ILocation loc, final CPrimitive type) {
		final String smtFunctionName = "to_fp";
		final ASTType[] paramASTTypes = new ASTType[2];
		paramASTTypes[0] = new NamedType(loc, BOOGIE_ROUNDING_MODE_IDENTIFIER, new ASTType[0]);
		paramASTTypes[1] = new PrimitiveType(loc, SFO.REAL);
		final FloatingPointSize fps = mTypeSizes.getFloatingPointSize(type.getType());
		final Attribute[] attributes = generateAttributes(loc, mOverapproximateFloatingPointOperations, smtFunctionName,
				new int[] { fps.getExponent(), fps.getSignificant() });
		final ASTType resultASTType = mTypeHandler.cType2AstType(loc, type);
		mFunctionDeclarations.declareFunction(loc, SFO.getBoogieFunctionName(smtFunctionName, type), attributes,
				resultASTType, paramASTTypes);
	}

	private void declareFloatingPointConstructorFromBitvec(final ILocation loc, final CPrimitive type) {
		final String smtFunctionName = "fp";
		final FloatingPointSize fps = mTypeSizes.getFloatingPointSize(type.getType());
		final ASTType[] paramASTTypes = new ASTType[3];
		paramASTTypes[0] = new PrimitiveType(loc, "bv1");
		paramASTTypes[1] = new PrimitiveType(loc, "bv" + fps.getExponent());
		paramASTTypes[2] = new PrimitiveType(loc, "bv" + (fps.getSignificant() - 1));
		final Attribute[] attributes =
				generateAttributes(loc, mOverapproximateFloatingPointOperations, smtFunctionName, null);
		final ASTType resultASTType = mTypeHandler.cType2AstType(loc, type);
		mFunctionDeclarations.declareFunction(loc, SFO.getBoogieFunctionName(smtFunctionName, type), attributes,
				resultASTType, paramASTTypes);
	}

	@Override
	public void convertIntToInt_NonBool(final ILocation loc, final ExpressionResult operand,
			final CPrimitive resultType) {
		if (resultType == null) {
			throw new UnsupportedOperationException("non-primitive types not supported yet " + resultType);
		}
		final CPrimitive resultPrimitive = resultType;
		if (resultPrimitive.getGeneralType() != CPrimitiveCategory.INTTYPE) {
			throw new UnsupportedOperationException("non-integer types not supported yet " + resultType);
		}

		final int resultLength = mTypeSizes.getSize(resultPrimitive.getType()) * 8;
		final int operandLength = mTypeSizes.getSize(((CPrimitive) operand.mLrVal.getCType()).getType()) * 8;

		if (resultLength == operandLength) {
			final RValue oldRValue = (RValue) operand.mLrVal;
			final RValue rVal = new RValue(oldRValue.getValue(), resultType, oldRValue.isBoogieBool(),
					oldRValue.isIntFromPointer());
			operand.mLrVal = rVal;
		} else if (resultLength > operandLength) {
			extend(loc, operand, resultType, resultPrimitive, resultLength, operandLength);
		} else {
			final Expression bv = extractBits(loc, operand.mLrVal.getValue(), resultLength, 0);
			final RValue rVal = new RValue(bv, resultType);
			operand.mLrVal = rVal;
		}
	}

	@Override
	public void convertFloatToInt_NonBool(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		final String prefixedFunctionName =
				declareConversionFunction(loc, (CPrimitive) rexp.mLrVal.getCType(), newType);
		final Expression oldExpression = rexp.mLrVal.getValue();
		final IdentifierExpression roundingMode =
				new IdentifierExpression(null, BitvectorTranslation.BOOGIE_ROUNDING_MODE_RTZ);
		roundingMode.setDeclarationInformation(new DeclarationInformation(StorageClass.GLOBAL, null));
		final Expression resultExpression =
				new FunctionApplication(loc, prefixedFunctionName, new Expression[] { roundingMode, oldExpression });
		final RValue rValue = new RValue(resultExpression, newType, false, false);
		rexp.mLrVal = rValue;
	}

	@Override
	public void convertIntToFloat(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		final String prefixedFunctionName =
				declareConversionFunction(loc, (CPrimitive) rexp.mLrVal.getCType(), newType);
		final Expression oldExpression = rexp.mLrVal.getValue();
		final Expression resultExpression = new FunctionApplication(loc, prefixedFunctionName,
				new Expression[] { getRoundingMode(), oldExpression });
		final RValue rValue = new RValue(resultExpression, newType, false, false);
		rexp.mLrVal = rValue;
	}

	@Override
	public void convertFloatToFloat(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		final String prefixedFunctionName =
				declareConversionFunction(loc, (CPrimitive) rexp.mLrVal.getCType(), newType);
		final Expression oldExpression = rexp.mLrVal.getValue();
		final Expression resultExpression = new FunctionApplication(loc, prefixedFunctionName,
				new Expression[] { getRoundingMode(), oldExpression });
		final RValue rValue = new RValue(resultExpression, newType, false, false);
		rexp.mLrVal = rValue;
	}

	@Override
	public Expression extractBits(final ILocation loc, final Expression operand, final int high, final int low) {
		return ExpressionFactory.constructBitvectorAccessExpression(loc, operand, high, low);
	}

	private void extend(final ILocation loc, final ExpressionResult operand, final CType resultType,
			final CPrimitive resultPrimitive, final int resultLength, final int operandLength) {
		final int[] indices = new int[] { resultLength - operandLength };
		final String smtFunctionName;
		if (mTypeSizes.isUnsigned(((CPrimitive) operand.mLrVal.getCType()))) {
			smtFunctionName = "zero_extend";
		} else {
			smtFunctionName = "sign_extend";
		}
		final String boogieFunctionName = smtFunctionName + "From"
				+ mFunctionDeclarations.computeBitvectorSuffix(loc, (CPrimitive) operand.mLrVal.getCType()) + "To"
				+ mFunctionDeclarations.computeBitvectorSuffix(loc, resultPrimitive);
		declareBitvectorFunction(loc, smtFunctionName, boogieFunctionName, false, resultPrimitive, indices,
				(CPrimitive) operand.mLrVal.getCType());
		final FunctionApplication func = new FunctionApplication(loc,
				SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName, new Expression[] { operand.mLrVal.getValue() });
		final RValue rVal = new RValue(func, resultType);
		operand.mLrVal = rVal;
	}

	@Override
	public BigInteger extractIntegerValue(final Expression expr, CType cType, final IASTNode hook) {
		if (cType.isIntegerType()) {
			cType = CEnum.replaceEnumWithInt(cType);
			if (expr instanceof BitvecLiteral) {
				final BigInteger value = new BigInteger(((BitvecLiteral) expr).getValue());
				if (mTypeSizes.isUnsigned(((CPrimitive) cType))) {
					if (value.signum() < 0) {
						throw new UnsupportedOperationException("negative value");
					}
					return value;
				}
				return value;
			}
			return null;
		}
		return null;
	}

	@Override
	public CPrimitive getCTypeOfPointerComponents() {
		// 2015-10-29 Matthias: using int is unsound on 64bit systems, but it
		// probably saves a lot of conversions and I guess this unsoundness
		// is never a problem in the SV-COMP and most other code
		return new CPrimitive(CPrimitives.INT);
	}

	@Override
	public void addAssumeValueInRangeStatements(final ILocation loc, final Expression expr, final CType ctype,
			final List<Statement> stmt) {
		// do nothing. not needed for bitvectors
	}

	@Override
	public void addAssumeValueInRangeStatements(final ILocation loc, final Expression expr, final CType ctype,
			final ExpressionResultBuilder expressionResultBuilder) {
		// do nothing. not needed for bitvectors
	}

	@Override
	public Expression concatBits(final ILocation loc, final List<Expression> dataChunks, final int size) {
		Expression result;
		final Iterator<Expression> it = dataChunks.iterator();
		result = it.next();
		while (it.hasNext()) {
			final Expression nextChunk = it.next();
			result = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.BITVECCONCAT, result,
					nextChunk);
		}
		return result;
	}

	@Override
	public Expression signExtend(final ILocation loc, final Expression operand, final int bitsBefore,
			final int bitsAfter) {
		final String smtFunctionName = "sign_extend";
		final ASTType resultType =
				((TypeHandler) mTypeHandler).bytesize2asttype(loc, CPrimitiveCategory.INTTYPE, bitsAfter / 8);
		final ASTType inputType =
				((TypeHandler) mTypeHandler).bytesize2asttype(loc, CPrimitiveCategory.INTTYPE, bitsBefore / 8);
		final String boogieFunctionName = smtFunctionName + "From" + bitsBefore + "To" + bitsAfter;
		if (!mFunctionDeclarations.getDeclaredFunctions()
				.containsKey(SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName)) {
			final int[] indices = new int[] { bitsAfter - bitsBefore };
			final Attribute[] attributes = generateAttributes(loc, false, smtFunctionName, indices);
			mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName, attributes,
					resultType, inputType);
		}
		return new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName,
				new Expression[] { operand });
	}

	@Override
	public Expression erazeBits(final ILocation loc, final Expression value, final CPrimitive cType, 
			final int remainingWith, final IASTNode hook) {
		final BigInteger bitmaskNumber = BigInteger.valueOf(2).pow(remainingWith).subtract(BigInteger.ONE);
		final Expression bitmask = constructLiteralForIntegerType(loc, cType, bitmaskNumber);
		final Expression result = constructBinaryBitwiseExpression(loc, IASTBinaryExpression.op_binaryAnd, value, cType,
				bitmask, cType, hook);
		return result;
	}

	@Override
	public Expression constructBinaryComparisonFloatingPointExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		if (!mFunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}

		boolean isNegated = false;
		final String smtFunctionName;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_equals:
			smtFunctionName = "fp.eq";
			break;
		case IASTBinaryExpression.op_notequals:
			smtFunctionName = "fp.eq";
			isNegated = true;
			break;
		case IASTBinaryExpression.op_greaterEqual:
			smtFunctionName = "fp.geq";
			break;
		case IASTBinaryExpression.op_greaterThan:
			smtFunctionName = "fp.gt";
			break;
		case IASTBinaryExpression.op_lessEqual:
			smtFunctionName = "fp.leq";
			break;
		case IASTBinaryExpression.op_lessThan:
			smtFunctionName = "fp.lt";
			break;
		default:
			throw new AssertionError("unknown operation " + nodeOperator);
		}

		declareFloatingPointFunction(loc, smtFunctionName, true, false, new CPrimitive(CPrimitives.BOOL), null, type1,
				type2);
		Expression result = new FunctionApplication(loc, SFO.getBoogieFunctionName(smtFunctionName, type1),
				new Expression[] { exp1, exp2 });

		if (isNegated) {
			result = ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, result);
		}
		return result;
	}

	@Override
	public Expression constructUnaryFloatingPointExpression(final ILocation loc, final int nodeOperator,
			final Expression exp, final CPrimitive type) {
		final Expression result;
		final String smtFunctionName;
		switch (nodeOperator) {
		case IASTUnaryExpression.op_minus:
			smtFunctionName = "fp.neg";
			break;
		default:
			final String msg = "Unknown or unsupported unary expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		declareFloatingPointFunction(loc, smtFunctionName, false, false, type, null, type);
		result = new FunctionApplication(loc, SFO.getBoogieFunctionName(smtFunctionName, type),
				new Expression[] { exp });
		return result;
	}

	@Override
	public Expression constructArithmeticFloatingPointExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		FunctionApplication result;
		if (!mFunctionDeclarations.checkParameters(type1, type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " " + type2);
		}
		boolean isRounded = true;
		final String smtFunctionName;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
			smtFunctionName = "fp.sub";
			break;
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
			smtFunctionName = "fp.mul";
			break;
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide:
			smtFunctionName = "fp.div";
			break;
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
			smtFunctionName = "fp.rem";
			isRounded = false;
			break;
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			smtFunctionName = "fp.add";
			break;
		default:
			final String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		if (isRounded) {
			declareFloatingPointFunction(loc, smtFunctionName, false, isRounded, type1, null, type1, type2);
			result = new FunctionApplication(loc, SFO.getBoogieFunctionName(smtFunctionName, type1),
					new Expression[] { getRoundingMode(), exp1, exp2 });
		} else {
			declareFloatingPointFunction(loc, smtFunctionName, false, isRounded, type1, null, type1, type2);
			result = new FunctionApplication(loc, SFO.getBoogieFunctionName(smtFunctionName, type1),
					new Expression[] { exp1, exp2 });
		}
		return result;
	}

	@Override
	public Expression constructBinaryEqualityExpressionFloating(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CType type1, final Expression exp2, final CType type2) {
		return constructBinaryComparisonFloatingPointExpression(loc, nodeOperator, exp1, (CPrimitive) type1, exp2,
				(CPrimitive) type2);
	}

	@Override
	public Expression constructBinaryEqualityExpressionInteger(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CType type1, final Expression exp2, final CType type2) {
		if (nodeOperator == IASTBinaryExpression.op_equals) {
			return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, exp1, exp2);
		} else if (nodeOperator == IASTBinaryExpression.op_notequals) {
			return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, exp1, exp2);
		} else {
			throw new IllegalArgumentException("operator is neither equals nor not equals");
		}
	}

	@Override
	protected String declareConversionFunction(final ILocation loc, final CPrimitive oldType,
			final CPrimitive newType) {

		final String functionName = "convert" + oldType.toString() + "To" + newType.toString();
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {

			final Attribute[] attributes;
			final ASTType paramASTType = mTypeHandler.cType2AstType(loc, oldType);
			final ASTType roundingMode = new NamedType(loc, BOOGIE_ROUNDING_MODE_IDENTIFIER, new ASTType[0]);
			if (newType.isFloatingType()) {
				final int[] indices = new int[2];
				final FloatingPointSize fps = mTypeSizes.getFloatingPointSize(newType.getType());
				indices[0] = fps.getExponent();
				indices[1] = fps.getSignificant();
				if (oldType.isIntegerType() && mTypeSizes.isUnsigned(oldType)) {
					attributes =
							generateAttributes(loc, mOverapproximateFloatingPointOperations, "to_fp_unsigned", indices);
				} else {
					attributes = generateAttributes(loc, mOverapproximateFloatingPointOperations, "to_fp", indices);
				}
			} else if (newType.isIntegerType()) {
				final String conversionFunction;
				if (mTypeSizes.isUnsigned(newType)) {
					conversionFunction = "fp.to_ubv";
				} else {
					conversionFunction = "fp.to_sbv";
				}
				final Integer bytesize = mTypeSizes.getSize(newType.getType());
				final int bitsize = bytesize * 8;
				attributes = generateAttributes(loc, mOverapproximateFloatingPointOperations, conversionFunction,
						new int[] { bitsize });
			} else {
				throw new AssertionError("unhandled case");
			}
			final ASTType[] params = new ASTType[] { roundingMode, paramASTType };
			final ASTType resultASTType = mTypeHandler.cType2AstType(loc, newType);

			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultASTType, params);
		}
		return prefixedFunctionName;
	}

	@Override
	public ExpressionResult createNanOrInfinity(final ILocation loc, final String name) {
		final String smtFunctionName;
		final CPrimitive type;
		if (name.equals("INFINITY") || name.equals("inf") || name.equals("inff")) {
			smtFunctionName = SMT_LIB_PLUS_INF;
			type = new CPrimitive(CPrimitives.DOUBLE);
		} else if (name.equals("NAN") || name.equals("nan")) {
			smtFunctionName = SMT_LIB_NAN;
			type = new CPrimitive(CPrimitives.DOUBLE);
		} else if (name.equals("nanl")) {
			smtFunctionName = SMT_LIB_NAN;
			type = new CPrimitive(CPrimitives.LONGDOUBLE);
		} else if (name.equals("nanf")) {
			smtFunctionName = SMT_LIB_NAN;
			type = new CPrimitive(CPrimitives.FLOAT);
		} else {
			throw new IllegalArgumentException("not a nan or infinity type");
		}
		declareFloatConstant(loc, smtFunctionName, type);
		final FunctionApplication func =
				new FunctionApplication(loc, SFO.getBoogieFunctionName(smtFunctionName, type), new Expression[] {});
		return new ExpressionResult(new RValue(func, type));
	}

	public void declareFloatConstant(final ILocation loc, final String smtFunctionName, final CPrimitive type) {
		final FloatingPointSize fps = mTypeSizes.getFloatingPointSize(type.getType());
		final Attribute[] attributes = generateAttributes(loc, mOverapproximateFloatingPointOperations, smtFunctionName,
				new int[] { fps.getExponent(), fps.getSignificant() });
		final ASTType asttype = mTypeHandler.cType2AstType(loc, type);
		getFunctionDeclarations().declareFunction(loc, SFO.getBoogieFunctionName(smtFunctionName, type), attributes,
				asttype);
	}

	@Override
	public Expression getRoundingMode() {
		return mRoundingMode;
	}

	@Override
	public RValue constructOtherUnaryFloatOperation(final ILocation loc, final FloatFunction floatFunction,
			final RValue argument) {
		if ("sqrt".equals(floatFunction.getFunctionName())) {
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType();
			final String smtFunctionName = "fp.sqrt";
			declareFloatingPointFunction(loc, smtFunctionName, false, true, argumentType, null, argumentType);
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType();
			final Expression expr = new FunctionApplication(loc, boogieFunctionName,
					new Expression[] { getRoundingMode(), argument.getValue() });
			return new RValue(expr, resultType);
		} else if ("fabs".equals(floatFunction.getFunctionName())) {
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType();
			final String smtFunctionName = "fp.abs";

			declareFloatingPointFunction(loc, smtFunctionName, false, false, argumentType, null, argumentType);
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType();
			final Expression expr =
					new FunctionApplication(loc, boogieFunctionName, new Expression[] { argument.getValue() });
			return new RValue(expr, resultType);
		} else if ("isnan".equals(floatFunction.getFunctionName())) {
			final String smtFunctionName = "fp.isNaN";
			return constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
		} else if ("isinf".equals(floatFunction.getFunctionName())) {
			final String smtFunctionName = "fp.isInfinite";
			return constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
		} else if ("isnormal".equals(floatFunction.getFunctionName())) {
			final String smtFunctionName = "fp.isNormal";
			return constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
		} else if ("isfinite".equals(floatFunction.getFunctionName())
				|| "finite".equals(floatFunction.getFunctionName())) {
			final Expression isNormal;
			{
				final String smtFunctionName = "fp.isNormal";
				final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
				isNormal = rvalue.getValue();
			}
			final Expression isSubnormal;
			{
				final String smtFunctionName = "fp.isSubnormal";
				final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
				isSubnormal = rvalue.getValue();
			}
			final Expression isZero;
			{
				final String smtFunctionName = "fp.isZero";
				final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
				isZero = rvalue.getValue();
			}
			final Expression resultExpr = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, isNormal, isSubnormal), isZero);
			return new RValue(resultExpr, new CPrimitive(CPrimitives.INT), true);
		} else if ("fpclassify".equals(floatFunction.getFunctionName())) {
			final Expression isInfinite;
			{
				final String smtFunctionName = "fp.isInfinite";
				final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
				isInfinite = rvalue.getValue();
			}
			final Expression isNan;
			{
				final String smtFunctionName = "fp.isNaN";
				final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
				isNan = rvalue.getValue();
			}
			final Expression isNormal;
			{
				final String smtFunctionName = "fp.isNormal";
				final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
				isNormal = rvalue.getValue();
			}
			final Expression isSubnormal;
			{
				final String smtFunctionName = "fp.isSubnormal";
				final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
				isSubnormal = rvalue.getValue();
			}
			// final Expression isZero;
			// {
			// final String smtLibFunctionName = "fp.isZero";
			// final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtLibFunctionName, argument);
			// isZero = rvalue.getValue();
			// }
			final Expression resultExpr = ExpressionFactory.newIfThenElseExpression(loc, isInfinite,
					handleNumberClassificationMacro(loc, "FP_INFINITE").getValue(),
					ExpressionFactory.newIfThenElseExpression(loc, isNan,
							handleNumberClassificationMacro(loc, "FP_NAN").getValue(),
							ExpressionFactory.newIfThenElseExpression(loc, isNormal,
									handleNumberClassificationMacro(loc, "FP_NORMAL").getValue(),
									ExpressionFactory.newIfThenElseExpression(loc, isSubnormal,
											handleNumberClassificationMacro(loc, "FP_SUBNORMAL").getValue(),
											handleNumberClassificationMacro(loc, "FP_ZERO").getValue()))));
			return new RValue(resultExpr, new CPrimitive(CPrimitives.INT));
		} else if ("signbit".equals(floatFunction.getFunctionName())) {
			final Expression isNegative;
			{
				final String smtFunctionName = "fp.isNegative";
				final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
				isNegative = rvalue.getValue();
			}
			final CPrimitive cPrimitive = new CPrimitive(CPrimitives.INT);
			final Expression resultExpr = ExpressionFactory.newIfThenElseExpression(loc, isNegative,
					constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ONE),
					constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ZERO));
			return new RValue(resultExpr, cPrimitive);
		}
		throw new UnsupportedOperationException("not yet supported float operation " + floatFunction.getFunctionName());
	}

	private static void checkIsFloatPrimitive(final RValue argument) {
		if (!(argument.getCType() instanceof CPrimitive)
				|| !((CPrimitive) argument.getCType()).getType().isFloatingtype()) {
			throw new IllegalArgumentException(
					"can apply float operation only to floating type, but saw " + argument.getCType());
		}
	}

	@Override
	public RValue constructOtherBinaryFloatOperation(final ILocation loc, final FloatFunction floatFunction,
			final RValue first, final RValue second) {
		// TODO Auto-generated method stub
		switch (floatFunction.getFunctionName()) {
		case "fmin":
			return delegateOtherBinaryFloatOperationToSmt(loc, first, second, "fp.min");
		case "fmax":
			return delegateOtherBinaryFloatOperationToSmt(loc, first, second, "fp.max");
		default:
			throw new UnsupportedOperationException(
					"not yet supported float operation " + floatFunction.getFunctionName());
		}
	}

	private RValue delegateOtherBinaryFloatOperationToSmt(final ILocation loc, final RValue first, final RValue second,
			final String smtFunctionName) {
		checkIsFloatPrimitive(first);
		checkIsFloatPrimitive(second);
		final CPrimitive firstArgumentType = (CPrimitive) first.getCType();
		final CPrimitive secondArgumentType = (CPrimitive) first.getCType();
		if (!firstArgumentType.equals(secondArgumentType)) {
			throw new IllegalArgumentException("No mixed type arguments allowed");
		}
		declareFloatingPointFunction(loc, smtFunctionName, false, false, firstArgumentType, null, firstArgumentType,
				secondArgumentType);
		final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, firstArgumentType);
		final CPrimitive resultType = firstArgumentType;
		final Expression expr = new FunctionApplication(loc, boogieFunctionName,
				new Expression[] { first.getValue(), second.getValue() });
		return new RValue(expr, resultType);
	}

	private RValue constructSmtFloatClassificationFunction(final ILocation loc, final String smtFunctionName,
			final RValue argument) {
		final CPrimitive argumentCType = (CPrimitive) argument.getCType();
		final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentCType);
		final CPrimitive resultCType = new CPrimitive(CPrimitives.INT);
		final ASTType resultBoogieType = new PrimitiveType(loc, SFO.BOOL);
		final Attribute[] attributes =
				generateAttributes(loc, mOverapproximateFloatingPointOperations, smtFunctionName, null);
		final ASTType paramBoogieType = mTypeHandler.cType2AstType(loc, argumentCType);
		getFunctionDeclarations().declareFunction(loc, boogieFunctionName, attributes, resultBoogieType,
				paramBoogieType);
		final Expression expr =
				new FunctionApplication(loc, boogieFunctionName, new Expression[] { argument.getValue() });
		return new RValue(expr, resultCType, true);
	}

	@Override
	public Expression transformBitvectorToFloat(final ILocation loc, final Expression bitvector,
			final CPrimitives floatType) {
		final FloatingPointSize floatingPointSize = mTypeSizes.getFloatingPointSize(floatType);
		final Expression significantBits = extractBits(loc, bitvector, floatingPointSize.getSignificant() - 1, 0);
		final Expression exponentBits =
				extractBits(loc, bitvector, floatingPointSize.getSignificant() - 1 + floatingPointSize.getExponent(),
						floatingPointSize.getSignificant() - 1);
		final Expression signBit = extractBits(loc, bitvector,
				floatingPointSize.getSignificant() - 1 + floatingPointSize.getExponent() + 1,
				floatingPointSize.getSignificant() - 1 + floatingPointSize.getExponent());
		final String smtFunctionName = "fp";
		final Expression result =
				new FunctionApplication(loc, SFO.getBoogieFunctionName(smtFunctionName, new CPrimitive(floatType)),
						new Expression[] { signBit, exponentBits, significantBits });
		return result;

	}

	@Override
	public Expression transformFloatToBitvector(final ILocation loc, final Expression value,
			final CPrimitives cprimitive) {
		final String smtFunctionName = "fp.to_ieee_bv";
		final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, new CPrimitive(cprimitive));

		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(boogieFunctionName)) {
			final int bytesize = mTypeSizes.getSize(cprimitive);
			final ASTType bvType =
					((TypeHandler) mTypeHandler).bytesize2asttype(loc, cprimitive.getPrimitiveCategory(), bytesize);
			final ASTType paramASTType = mTypeHandler.cType2AstType(loc, new CPrimitive(cprimitive));
			final ASTType[] params = new ASTType[] { paramASTType };
			final Attribute[] attributes =
					generateAttributes(loc, mOverapproximateFloatingPointOperations, smtFunctionName, null);
			mFunctionDeclarations.declareFunction(loc, boogieFunctionName, attributes, bvType, params);
		}
		final Expression result = new FunctionApplication(loc, boogieFunctionName, new Expression[] { value });
		return result;
	}

	/**
	 * Declare a given list of binary bitvector functions for all integer datatypes. We use this as a workaround for the
	 * following problem. Usually, we only declare the bitvector functions that occur in the program. However, if an
	 * analysis constructs a proof in form of a Hoare annotation, this proof may also use other functions and our
	 * backtranslation crashes. 2017-05-03 Matthias: Currently it seems that it is sufficient to add only bvadd for all
	 * integer datatypes.
	 */
	public void declareBinaryBitvectorFunctionsForAllIntegerDatatypes(final ILocation loc,
			final String[] bitvectorFunctions) {
		for (final String funcname : bitvectorFunctions) {
			for (final CPrimitive.CPrimitives cPrimitive : CPrimitive.CPrimitives.values()) {
				final CPrimitive cPrimitiveO = new CPrimitive(cPrimitive);
				if (cPrimitiveO.getGeneralType() == CPrimitiveCategory.INTTYPE) {
					declareBitvectorFunction(loc, funcname,
							funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, cPrimitiveO, cPrimitiveO),
							false, cPrimitiveO, null, cPrimitiveO, cPrimitiveO);
				}
			}
		}
	}



}
