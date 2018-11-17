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
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieTypeConstructor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes.FloatingPointSize;
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

public class BitvectorTranslation extends ExpressionTranslation {

	/**
	 * Describes the SMT constants we use to represent the rounding mode of floating point operations.
	 *
	 * Based on http://www.cprover.org/SMT-LIB-Float/smt-fpa.pdf Section 3.2
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum SmtRoundingMode {

	/**
	 * Round towards the nearest, tie to even.
	 */
	RNE("roundNearestTiesToEven"),

	/**
	 * Round toward nearest, tie to away.
	 */
	RNA("roundNearestTiesToAway"),

	/**
	 * Round toward positive.
	 *
	 * In this mode, a number r is rounded to the least upper floating-point bound.
	 */
	RTP("roundTowardPositive"),

	/**
	 * Round toward negative.
	 *
	 * In this mode, a number r is rounded to the greatest lower floating-point bound.
	 */
	RTN("roundTowardNegative"),

	/**
	 * Round toward zero.
	 *
	 * In this mode, a number r is rounded to the closest FP number whose absolute value is closest to zero.
	 */
	RTZ("roundTowardZero");

		private final String mSmtIdentifier;
		private final IdentifierExpression mBoogieExpr;
		private final VarList mVarlist;

		private SmtRoundingMode(final String smtIdentifier) {
			mSmtIdentifier = smtIdentifier;
			final CACSLLocation loc = LocationFactory.createIgnoreCLocation();
			final String boogieId = SFO.AUXILIARY_FUNCTION_PREFIX + smtIdentifier;
			mBoogieExpr = ExpressionFactory.constructIdentifierExpression(loc, ROUNDING_MODE_BOOGIE_TYPE, boogieId,
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
			mVarlist = new VarList(loc, new String[] { boogieId }, ROUNDING_MODE_BOOGIE_TYPE.toASTType(loc));
		}

		public String getSmtIdentifier() {
			return mSmtIdentifier;
		}

		public String getBoogieIdentifier() {
			return mBoogieExpr.getIdentifier();
		}

		public IdentifierExpression getBoogieIdentifierExpression() {
			return mBoogieExpr;
		}

		public VarList getBoogieVarlist() {
			return mVarlist;
		}

	}

	public static final String ROUNDING_MODE_BOOGIE_TYPE_IDENTIFIER = "FloatRoundingMode";
	public static final String ROUNDING_MODE_SMT_TYPE_IDENTIFIER = "RoundingMode";
	public static final BoogieType ROUNDING_MODE_BOOGIE_TYPE = BoogieType.createConstructedType(
			new BoogieTypeConstructor(ROUNDING_MODE_BOOGIE_TYPE_IDENTIFIER, false, 0, new int[0]));
	public static final ASTType ROUNDING_MODE_BOOGIE_AST_TYPE =
			ROUNDING_MODE_BOOGIE_TYPE.toASTType(LocationFactory.createIgnoreCLocation());

	public static final String SMT_LIB_NAN = "NaN";
	public static final String SMT_LIB_PLUS_INF = "+oo";
	public static final String SMT_LIB_MINUS_INF = "-oo";
	public static final String SMT_LIB_PLUS_ZERO = "+zero";
	public static final String SMT_LIB_MINUS_ZERO = "-zero";

	private final IdentifierExpression mActiveRoundingMode;

	public BitvectorTranslation(final TypeSizes typeSizeConstants, final TranslationSettings translationSettings,
			final FlatSymbolTable symboltable, final ITypeHandler typeHandler) {
		super(typeSizeConstants, translationSettings, typeHandler, symboltable);
		// TODO: Depending on the setting, either set this to one of the constants or to the global variable.
		mActiveRoundingMode = SmtRoundingMode.RNE.getBoogieIdentifierExpression();
	}

	@Override
	public RValue translateIntegerLiteral(final ILocation loc, final String val) {
		final RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, true, mTypeSizes);
		return rVal;
	}

	@Override
	public Expression constructLiteralForFloatingType(final ILocation loc, final CPrimitive type,
			final BigDecimal value) {
		if (mSettings.overapproximateFloatingPointOperations()) {
			return super.constructOverapproximationFloatLiteral(loc, value.toString(), type);
		}
		final Expression[] arguments;
		final String smtFunctionName;
		if (value.compareTo(BigDecimal.ZERO) == 0) {
			smtFunctionName = SMT_LIB_PLUS_ZERO;
			arguments = new Expression[] {};
		} else {
			smtFunctionName = "to_fp";
			final Expression realValue = ExpressionFactory.createRealLiteral(loc, value.toString());
			arguments = new Expression[] { getRoundingMode(), realValue };
		}
		final String functionName = SFO.getBoogieFunctionName(smtFunctionName, type);
		return ExpressionFactory.constructFunctionApplication(loc, functionName, arguments,
				mTypeHandler.getBoogieTypeForCType(type));
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
		final String fullFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + functionName
				+ mFunctionDeclarations.computeBitvectorSuffix(loc, type1, type2);
		final Expression result = ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
				new Expression[] { exp1, exp2 }, BoogieType.TYPE_BOOL);
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
		final String fullFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname
				+ mFunctionDeclarations.computeBitvectorSuffix(loc, typeLeft, typeRight);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
				new Expression[] { left, right }, mTypeHandler.getBoogieTypeForCType(typeLeft));
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
		final String fullFunctionName =
				SFO.AUXILIARY_FUNCTION_PREFIX + funcname + mFunctionDeclarations.computeBitvectorSuffix(loc, type);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
				new Expression[] { expr }, mTypeHandler.getBoogieTypeForCType(type));
		return func;
	}

	@Override
	public Expression constructArithmeticIntegerExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
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
		final String fullFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname
				+ mFunctionDeclarations.computeBitvectorSuffix(loc, type1, type2);
		return ExpressionFactory.constructFunctionApplication(loc, fullFunctionName, new Expression[] { exp1, exp2 },
				mTypeHandler.getBoogieTypeForCType(type1));
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
			final CPrimitive... paramCType) {
		declareFloatingPointFunction(loc, smtFunctionName, boogieResultTypeBool, isRounded, resultCType, null,
				paramCType);
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
				generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(), smtFunctionName, indices);
		if (isRounded) {
			final ASTType[] paramASTTypes = new ASTType[paramCType.length + 1];
			final ASTType resultASTType = mTypeHandler.cType2AstType(loc, resultCType);
			int counter = 1;
			paramASTTypes[0] = BitvectorTranslation.ROUNDING_MODE_BOOGIE_AST_TYPE;
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

	@Override
	public void declareFloatingPointConstructors(final ILocation loc, final CPrimitive type) {
		declareFloatingPointConstructorFromBitvec(loc, type);
		declareFloatingPointConstructorFromReal(loc, type);
	}

	private void declareFloatingPointConstructorFromReal(final ILocation loc, final CPrimitive type) {
		final String smtFunctionName = "to_fp";
		final ASTType[] paramASTTypes = new ASTType[2];
		paramASTTypes[0] = BitvectorTranslation.ROUNDING_MODE_BOOGIE_AST_TYPE;
		paramASTTypes[1] = new PrimitiveType(loc, BoogieType.TYPE_REAL, SFO.REAL);
		final FloatingPointSize fps = mTypeSizes.getFloatingPointSize(type.getType());
		final Attribute[] attributes = generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(),
				smtFunctionName, new int[] { fps.getExponent(), fps.getSignificant() });
		final ASTType resultASTType = mTypeHandler.cType2AstType(loc, type);
		mFunctionDeclarations.declareFunction(loc, SFO.getBoogieFunctionName(smtFunctionName, type), attributes,
				resultASTType, paramASTTypes);
	}

	private void declareFloatingPointConstructorFromBitvec(final ILocation loc, final CPrimitive type) {
		final String smtFunctionName = "fp";
		final FloatingPointSize fps = mTypeSizes.getFloatingPointSize(type.getType());
		final ASTType[] paramASTTypes = new ASTType[3];
		paramASTTypes[0] = new PrimitiveType(loc, BoogieType.createBitvectorType(1), "bv1");
		paramASTTypes[1] =
				new PrimitiveType(loc, BoogieType.createBitvectorType(fps.getExponent()), "bv" + fps.getExponent());
		paramASTTypes[2] = new PrimitiveType(loc, BoogieType.createBitvectorType(fps.getSignificant() - 1),
				"bv" + (fps.getSignificant() - 1));
		final Attribute[] attributes =
				generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(), smtFunctionName, null);
		final ASTType resultASTType = mTypeHandler.cType2AstType(loc, type);
		mFunctionDeclarations.declareFunction(loc, SFO.getBoogieFunctionName(smtFunctionName, type), attributes,
				resultASTType, paramASTTypes);
	}

	@Override
	public ExpressionResult convertIntToInt_NonBool(final ILocation loc, final ExpressionResult operand,
			final CPrimitive resultType) {
		if (resultType == null) {
			throw new UnsupportedOperationException("non-primitive types not supported yet " + resultType);
		}
		final CPrimitive resultPrimitive = resultType;
		if (resultPrimitive.getGeneralType() != CPrimitiveCategory.INTTYPE) {
			throw new UnsupportedOperationException("non-integer types not supported yet " + resultType);
		}

		final int resultLength = mTypeSizes.getSize(resultPrimitive.getType()) * 8;

		final int operandLength =
				mTypeSizes.getSize(((CPrimitive) operand.getLrValue().getCType().getUnderlyingType()).getType()) * 8;

		if (resultLength == operandLength) {
			final RValue oldRValue = (RValue) operand.getLrValue();
			final RValue rVal = new RValue(oldRValue.getValue(), resultType, oldRValue.isBoogieBool(),
					oldRValue.isIntFromPointer());
			return new ExpressionResultBuilder().addAllExceptLrValue(operand).setLrValue(rVal).build();
		}
		if (resultLength > operandLength) {
			return extend(loc, operand, resultType, resultPrimitive, resultLength, operandLength);
		}
		final Expression bv = extractBits(loc, operand.getLrValue().getValue(), resultLength, 0);
		final RValue rVal = new RValue(bv, resultType);
		return new ExpressionResultBuilder().addAllExceptLrValue(operand).setLrValue(rVal).build();
	}

	@Override
	public ExpressionResult convertFloatToInt_NonBool(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		final String prefixedFunctionName =
				declareConversionFunction(loc, (CPrimitive) rexp.getLrValue().getCType().getUnderlyingType(), newType);
		final Expression oldExpression = rexp.getLrValue().getValue();

		// TODO double check if the type and location of roundingMode are well-chosen,
		// also see the constructor
		// BitvectorTranslation(..) for an analogous case
		final IdentifierExpression roundingMode = SmtRoundingMode.RTZ.getBoogieIdentifierExpression();
		final Expression resultExpression = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { roundingMode, oldExpression }, mTypeHandler.getBoogieTypeForCType(newType));
		final RValue rVal = new RValue(resultExpression, newType, false, false);
		return new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
	}

	@Override
	public ExpressionResult convertIntToFloat(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		final String prefixedFunctionName =
				declareConversionFunction(loc, (CPrimitive) rexp.getLrValue().getCType().getUnderlyingType(), newType);
		final Expression oldExpression = rexp.getLrValue().getValue();
		final Expression resultExpression = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { getRoundingMode(), oldExpression }, mTypeHandler.getBoogieTypeForCType(newType));
		final RValue rVal = new RValue(resultExpression, newType, false, false);
		return new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
	}

	@Override
	public ExpressionResult convertFloatToFloat(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		final String prefixedFunctionName =
				declareConversionFunction(loc, (CPrimitive) rexp.getLrValue().getCType().getUnderlyingType(), newType);
		final Expression oldExpression = rexp.getLrValue().getValue();
		final Expression resultExpression = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { getRoundingMode(), oldExpression }, mTypeHandler.getBoogieTypeForCType(newType));
		final RValue rVal = new RValue(resultExpression, newType, false, false);
		return new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
	}

	@Override
	public Expression extractBits(final ILocation loc, final Expression operand, final int high, final int low) {
		return ExpressionFactory.constructBitvectorAccessExpression(loc, operand, high, low);
	}

	private ExpressionResult extend(final ILocation loc, final ExpressionResult operand, final CType resultType,
			final CPrimitive resultPrimitive, final int resultLength, final int operandLength) {
		final int[] indices = new int[] { resultLength - operandLength };
		final String smtFunctionName;
		if (mTypeSizes.isUnsigned((CPrimitive) operand.getLrValue().getCType().getUnderlyingType())) {
			smtFunctionName = "zero_extend";
		} else {
			smtFunctionName = "sign_extend";
		}
		final String boogieFunctionName = smtFunctionName + "From"
				+ mFunctionDeclarations.computeBitvectorSuffix(loc,
						(CPrimitive) operand.getLrValue().getCType().getUnderlyingType())
				+ "To" + mFunctionDeclarations.computeBitvectorSuffix(loc, resultPrimitive);
		declareBitvectorFunction(loc, smtFunctionName, boogieFunctionName, false, resultPrimitive, indices,
				(CPrimitive) operand.getLrValue().getCType().getUnderlyingType());
		final String fullFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName;
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
				new Expression[] { operand.getLrValue().getValue() }, mTypeHandler.getBoogieTypeForCType(resultType));
		final RValue rVal = new RValue(func, resultType);
		return new ExpressionResultBuilder().addAllExceptLrValue(operand).setLrValue(rVal).build();
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
				((TypeHandler) mTypeHandler).byteSize2AstType(loc, CPrimitiveCategory.INTTYPE, bitsAfter / 8);
		final ASTType inputType =
				((TypeHandler) mTypeHandler).byteSize2AstType(loc, CPrimitiveCategory.INTTYPE, bitsBefore / 8);
		final String boogieFunctionName = smtFunctionName + "From" + bitsBefore + "To" + bitsAfter;
		if (!mFunctionDeclarations.getDeclaredFunctions()
				.containsKey(SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName)) {
			final int[] indices = new int[] { bitsAfter - bitsBefore };
			final Attribute[] attributes = generateAttributes(loc, false, smtFunctionName, indices);
			mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName, attributes,
					resultType, inputType);
		}
		final String fullFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + boogieFunctionName;
		return ExpressionFactory.constructFunctionApplication(loc, fullFunctionName, new Expression[] { operand },
				BoogieType.createBitvectorType(bitsAfter));
	}

	@Override
	public Expression eraseBits(final ILocation loc, final Expression value, final CPrimitive cType,
			final int remainingWith, final IASTNode hook) {
		final BigInteger bitmaskNumber = BigInteger.valueOf(2).pow(remainingWith).subtract(BigInteger.ONE);
		final Expression bitmask = mTypeSizes.constructLiteralForIntegerType(loc, cType, bitmaskNumber);
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

		declareFloatingPointFunction(loc, smtFunctionName, true, false, new CPrimitive(CPrimitives.BOOL), type1, type2);
		final String fullFunctionName = SFO.getBoogieFunctionName(smtFunctionName, type1);
		Expression result = ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
				new Expression[] { exp1, exp2 }, BoogieType.TYPE_BOOL);

		if (isNegated) {
			result = ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, result);
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
		declareFloatingPointFunction(loc, smtFunctionName, false, false, type, type);
		final String fullFunctionName = SFO.getBoogieFunctionName(smtFunctionName, type);
		result = ExpressionFactory.constructFunctionApplication(loc, fullFunctionName, new Expression[] { exp },
				mTypeHandler.getBoogieTypeForCType(type));
		return result;
	}

	@Override
	public Expression constructArithmeticFloatingPointExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
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
			declareFloatingPointFunction(loc, smtFunctionName, false, isRounded, type1, type1, type2);
			final String fullFunctionName = SFO.getBoogieFunctionName(smtFunctionName, type1);
			return ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
					new Expression[] { getRoundingMode(), exp1, exp2 }, mTypeHandler.getBoogieTypeForCType(type1));
		}
		declareFloatingPointFunction(loc, smtFunctionName, false, isRounded, type1, type1, type2);
		final String fullFunctionName = SFO.getBoogieFunctionName(smtFunctionName, type1);
		return ExpressionFactory.constructFunctionApplication(loc, fullFunctionName, new Expression[] { exp1, exp2 },
				mTypeHandler.getBoogieTypeForCType(type1));
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
			final ASTType roundingMode = BitvectorTranslation.ROUNDING_MODE_BOOGIE_AST_TYPE;
			if (newType.isFloatingType()) {
				final int[] indices = new int[2];
				final FloatingPointSize fps = mTypeSizes.getFloatingPointSize(newType.getType());
				indices[0] = fps.getExponent();
				indices[1] = fps.getSignificant();
				if (oldType.isIntegerType() && mTypeSizes.isUnsigned(oldType)) {
					attributes = generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(),
							"to_fp_unsigned", indices);
				} else {
					attributes = generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(), "to_fp",
							indices);
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
				attributes = generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(),
						conversionFunction, new int[] { bitsize });
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
		final String fullFunctionName = SFO.getBoogieFunctionName(smtFunctionName, type);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
				new Expression[] {}, mTypeHandler.getBoogieTypeForCType(type));
		return new ExpressionResult(new RValue(func, type));
	}

	public ExpressionResult createRoundingMode(final ILocation loc, final String name) {
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
		final String fullFunctionName = SFO.getBoogieFunctionName(smtFunctionName, type);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
				new Expression[] {}, mTypeHandler.getBoogieTypeForCType(type));
		return new ExpressionResult(new RValue(func, type));
	}

	@Override
	public void declareFloatConstant(final ILocation loc, final String smtFunctionName, final CPrimitive type) {
		final FloatingPointSize fps = mTypeSizes.getFloatingPointSize(type.getType());
		final Attribute[] attributes = generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(),
				smtFunctionName, new int[] { fps.getExponent(), fps.getSignificant() });
		final ASTType asttype = mTypeHandler.cType2AstType(loc, type);
		getFunctionDeclarations().declareFunction(loc, SFO.getBoogieFunctionName(smtFunctionName, type), attributes,
				asttype);
	}

	@Override
	public Expression getRoundingMode() {
		return mActiveRoundingMode;
	}

	@Override
	public RValue constructOtherUnaryFloatOperation(final ILocation loc, final FloatFunction floatFunction,
			final RValue argument) {
		if ("sqrt".equals(floatFunction.getFunctionName())) {
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType().getUnderlyingType();
			final String smtFunctionName = "fp.sqrt";
			declareFloatingPointFunction(loc, smtFunctionName, false, true, argumentType, argumentType);
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType().getUnderlyingType();
			final Expression expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { getRoundingMode(), argument.getValue() },
					mTypeHandler.getBoogieTypeForCType(resultType));
			return new RValue(expr, resultType);
		} else if ("trunc".equals(floatFunction.getFunctionName())) {
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType().getUnderlyingType();
			final String smtFunctionName = "fp.roundToIntegral";
			declareFloatingPointFunction(loc, smtFunctionName, false, true, argumentType, argumentType);
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType().getUnderlyingType();
			final Expression expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { SmtRoundingMode.RTZ.getBoogieIdentifierExpression(), argument.getValue() },
					mTypeHandler.getBoogieTypeForCType(resultType));
			return new RValue(expr, resultType);
		} else if ("round".equals(floatFunction.getFunctionName())) {
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType().getUnderlyingType();
			final String smtFunctionName = "fp.roundToIntegral";
			declareFloatingPointFunction(loc, smtFunctionName, false, true, argumentType, argumentType);
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType().getUnderlyingType();
			final Expression expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { SmtRoundingMode.RNA.getBoogieIdentifierExpression(), argument.getValue() },
					mTypeHandler.getBoogieTypeForCType(resultType));
			return new RValue(expr, resultType);
		} else if ("lround".equals(floatFunction.getFunctionName())) {
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType().getUnderlyingType();
			final String smtFunctionName = "fp.roundToIntegral";
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType().getUnderlyingType();

			declareFloatingPointFunction(loc, smtFunctionName, false, true, resultType, argumentType);
			final Expression expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { SmtRoundingMode.RNA.getBoogieIdentifierExpression(), argument.getValue() },
					mTypeHandler.getBoogieTypeForCType(resultType));

			final CPrimitive longResultType = new CPrimitive(CPrimitives.LONG);
			final String smtConvertTypeFunctionName = "fp.to_sbv";
			final String ConvertBoogieFunctionName = SFO.getBoogieFunctionName(smtConvertTypeFunctionName, resultType);
			declareFloatingPointFunction(loc, smtConvertTypeFunctionName, false, true, longResultType, resultType);
			final Expression convertExpr =
					ExpressionFactory.constructFunctionApplication(loc, ConvertBoogieFunctionName,
							new Expression[] { SmtRoundingMode.RNA.getBoogieIdentifierExpression(), expr },
							mTypeHandler.getBoogieTypeForCType(longResultType));

			return new RValue(convertExpr, longResultType);
		} else if ("llround".equals(floatFunction.getFunctionName())) {
			// TODO fix result type. fp.to_sbv. smt function to convert to long long??
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType().getUnderlyingType();
			final String smtFunctionName = "fp.roundToIntegral";
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType().getUnderlyingType();

			declareFloatingPointFunction(loc, smtFunctionName, false, false, resultType, argumentType);
			final Expression expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { SmtRoundingMode.RNA.getBoogieIdentifierExpression(), argument.getValue() },
					mTypeHandler.getBoogieTypeForCType(resultType));

			final CPrimitive longLongResultType = new CPrimitive(CPrimitives.LONGLONG);
			final String smtConvertTypeFunctionName = "fp.to_sbv";
			final String ConvertBoogieFunctionName = SFO.getBoogieFunctionName(smtConvertTypeFunctionName, resultType);
			declareFloatingPointFunction(loc, smtConvertTypeFunctionName, false, true, longLongResultType, resultType);
			final Expression convertExpr =
					ExpressionFactory.constructFunctionApplication(loc, ConvertBoogieFunctionName,
							new Expression[] { SmtRoundingMode.RNA.getBoogieIdentifierExpression(), expr },
							mTypeHandler.getBoogieTypeForCType(longLongResultType));

			return new RValue(convertExpr, longLongResultType);
		} else if ("floor".equals(floatFunction.getFunctionName())) {
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType().getUnderlyingType();
			final String smtFunctionName = "fp.roundToIntegral";

			// TODO: Its the wrong return type. We need to get the bv type for this float type and pass it to this
			// declare function thing.
			// We also need to declare the matching
			declareFloatingPointFunction(loc, smtFunctionName, false, true, argumentType, argumentType);
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType().getUnderlyingType();
			final Expression expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { SmtRoundingMode.RTN.getBoogieIdentifierExpression(), argument.getValue() },
					mTypeHandler.getBoogieTypeForCType(resultType));
			return new RValue(expr, resultType);
		} else if ("ceil".equals(floatFunction.getFunctionName())) {
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType().getUnderlyingType();
			final String smtFunctionName = "fp.roundToIntegral";
			declareFloatingPointFunction(loc, smtFunctionName, false, true, argumentType, argumentType);
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType().getUnderlyingType();
			final Expression expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { SmtRoundingMode.RTP.getBoogieIdentifierExpression(), argument.getValue() },
					mTypeHandler.getBoogieTypeForCType(resultType));
			return new RValue(expr, resultType);
		} else if ("sin".equals(floatFunction.getFunctionName())) {
			// TODO Create correct BoogieFunction using SMT functions. See
			// http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml
			// Check how sin in calculated in c source. I believe it is approximated with a polynomial
			// See Taylor's theorem
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType().getUnderlyingType();
			final String smtFunctionName = "fp.sin";
			declareFloatingPointFunction(loc, smtFunctionName, false, true, argumentType, argumentType);
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType().getUnderlyingType();
			final Expression expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { getRoundingMode(), argument.getValue() },
					mTypeHandler.getBoogieTypeForCType(resultType));
			return new RValue(expr, resultType);
		} else if ("fabs".equals(floatFunction.getFunctionName())) {
			checkIsFloatPrimitive(argument);
			final CPrimitive argumentType = (CPrimitive) argument.getCType().getUnderlyingType();
			final String smtFunctionName = "fp.abs";
			declareFloatingPointFunction(loc, smtFunctionName, false, false, argumentType, argumentType);
			final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentType);
			final CPrimitive resultType = (CPrimitive) argument.getCType().getUnderlyingType();
			final Expression expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { argument.getValue() }, mTypeHandler.getBoogieTypeForCType(resultType));
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
			// final RValue rvalue = constructSmtFloatClassificationFunction(loc,
			// smtLibFunctionName, argument);
			// isZero = rvalue.getValue();
			// }
			final Expression resultExpr = ExpressionFactory.constructIfThenElseExpression(loc, isInfinite,
					handleNumberClassificationMacro(loc, "FP_INFINITE").getValue(),
					ExpressionFactory.constructIfThenElseExpression(loc, isNan,
							handleNumberClassificationMacro(loc, "FP_NAN").getValue(),
							ExpressionFactory.constructIfThenElseExpression(loc, isNormal,
									handleNumberClassificationMacro(loc, "FP_NORMAL").getValue(),
									ExpressionFactory.constructIfThenElseExpression(loc, isSubnormal,
											handleNumberClassificationMacro(loc, "FP_SUBNORMAL").getValue(),
											handleNumberClassificationMacro(loc, "FP_ZERO").getValue()))));
			return new RValue(resultExpr, new CPrimitive(CPrimitives.INT));
		} else if ("signbit".equals(floatFunction.getFunctionName())) {
			final Expression isNegative;
			final String smtFunctionName = "fp.isNegative";
			final RValue rvalue = constructSmtFloatClassificationFunction(loc, smtFunctionName, argument);
			isNegative = rvalue.getValue();

			final CPrimitive cPrimitive = new CPrimitive(CPrimitives.INT);
			final Expression resultExpr = ExpressionFactory.constructIfThenElseExpression(loc, isNegative,
					mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ONE),
					mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ZERO));
			return new RValue(resultExpr, cPrimitive);
		}
		throw new UnsupportedOperationException("not yet supported float operation " + floatFunction.getFunctionName());
	}

	private static void checkIsFloatPrimitive(final RValue argument) {
		if (!(argument.getCType().getUnderlyingType() instanceof CPrimitive)
				|| !((CPrimitive) argument.getCType().getUnderlyingType()).getType().isFloatingtype()) {
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
		case "remainder":
			return delegateOtherBinaryFloatOperationToSmt(loc, first, second, "fp.rem");
		case "fmod":
			// fmod guarantees that the return value is the same sign as the first argument (x)
			// copies the sign of firts element to remainder value
			final RValue remainderValue = delegateOtherBinaryFloatOperationToSmt(loc, first, second, "fp.rem");
			final FloatFunction copySignFunction = FloatFunction.decode("copysign");
			return constructOtherBinaryFloatOperation(loc, copySignFunction, remainderValue, first);
		case "copysign":
			// if second is negative, return arithneg of abs(first), else return abs(first)
			final FloatFunction absfloatFunction = FloatFunction.decode("fabs");
			final RValue absoluteValue = constructOtherUnaryFloatOperation(loc, absfloatFunction, first);

			final Expression isNegativeSecond;
			final String smtNegativeFunctionName = "fp.isNegative";
			final RValue secondNegativeRvalue =
					constructSmtFloatClassificationFunction(loc, smtNegativeFunctionName, second);
			isNegativeSecond = secondNegativeRvalue.getValue();
			final CPrimitive resultType = (CPrimitive) first.getCType().getUnderlyingType();
			final Expression negative = constructUnaryFloatingPointExpression(loc, IASTUnaryExpression.op_minus,
					absoluteValue.getValue(), resultType);
			final Expression resultExpr = ExpressionFactory.constructIfThenElseExpression(loc, isNegativeSecond,
					negative, absoluteValue.getValue());
			return new RValue(resultExpr, resultType);
		case "fdim":
			// if first>second, first - second, else +0
			final CPrimitive typeFirst = (CPrimitive) first.getCType().getUnderlyingType();
			final CPrimitive typeSecond = (CPrimitive) second.getCType().getUnderlyingType();

			final Expression comparison = constructBinaryComparisonFloatingPointExpression(loc,
					IASTBinaryExpression.op_greaterThan, first.getValue(), typeFirst, second.getValue(), typeSecond);

			final Expression subtraction = constructArithmeticFloatingPointExpression(loc,
					IASTBinaryExpression.op_minus, first.getValue(), typeFirst, second.getValue(), typeSecond);

			final Expression zero = constructLiteralForFloatingType(loc, typeFirst, BigDecimal.ZERO);

			final Expression resultExprFdim =
					ExpressionFactory.constructIfThenElseExpression(loc, comparison, subtraction, zero);
			return new RValue(resultExprFdim, typeFirst);

		default:
			throw new UnsupportedOperationException(
					"not yet supported float operation " + floatFunction.getFunctionName());
		}

	}

	private RValue delegateOtherBinaryFloatOperationToSmt(final ILocation loc, final RValue first, final RValue second,
			final String smtFunctionName) {

		return delegateOtherBinaryFloatOperationToSmt(loc, first, second, smtFunctionName, false);
	}

	private RValue delegateOtherBinaryFloatOperationToSmt(final ILocation loc, final RValue first, final RValue second,
			final String smtFunctionName, final Boolean rounding) {
		checkIsFloatPrimitive(first);
		checkIsFloatPrimitive(second);
		final CPrimitive firstArgumentType = (CPrimitive) first.getCType().getUnderlyingType();

		final CPrimitive secondArgumentType = (CPrimitive) first.getCType().getUnderlyingType();
		if (!firstArgumentType.equals(secondArgumentType)) {
			throw new IllegalArgumentException("No mixed type arguments allowed");
		}
		declareFloatingPointFunction(loc, smtFunctionName, false, rounding, firstArgumentType, firstArgumentType,
				secondArgumentType);
		final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, firstArgumentType);
		final CPrimitive resultType = firstArgumentType;
		Expression expr;
		if (rounding) {
			expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { getRoundingMode(), first.getValue(), second.getValue() },
					mTypeHandler.getBoogieTypeForCType(resultType));
		} else {
			expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
					new Expression[] { first.getValue(), second.getValue() },
					mTypeHandler.getBoogieTypeForCType(resultType));
		}
		return new RValue(expr, resultType);
	}

	private RValue constructSmtFloatClassificationFunction(final ILocation loc, final String smtFunctionName,
			final RValue argument) {
		final CPrimitive argumentCType = (CPrimitive) argument.getCType().getUnderlyingType();
		final String boogieFunctionName = SFO.getBoogieFunctionName(smtFunctionName, argumentCType);
		final CPrimitive resultCType = new CPrimitive(CPrimitives.INT);
		final ASTType resultBoogieType = new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL);
		final Attribute[] attributes =
				generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(), smtFunctionName, null);
		final ASTType paramBoogieType = mTypeHandler.cType2AstType(loc, argumentCType);
		getFunctionDeclarations().declareFunction(loc, boogieFunctionName, attributes, resultBoogieType,
				paramBoogieType);
		final Expression expr = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
				new Expression[] { argument.getValue() }, BoogieType.TYPE_BOOL);
		return new RValue(expr, resultCType, true);
	}

	@Override
	public RValue constructBuiltinFegetround(final ILocation loc) {
		// see https://en.cppreference.com/w/c/types/limits/FLT_ROUNDS and
		// https://en.cppreference.com/w/c/numeric/fenv/feround

		final CPrimitive resultCType = new CPrimitive(CPrimitives.INT);
		Expression resultExpression;
		final CPrimitive cPrimitive = new CPrimitive(CPrimitives.INT);

		switch (((IdentifierExpression) getRoundingMode()).getIdentifier()) {
		case "~roundTowardZero":
			resultExpression = mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ONE);
			break;
		case "~roundNearestTiesToEven":
			resultExpression = mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ONE);
			break;
		case "~roundTowardPositive":
			resultExpression = mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, new BigInteger("2"));
			break;
		case "~roundTowardNegative":
			resultExpression = mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, new BigInteger("3"));
			break;
		default:
			resultExpression = mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, new BigInteger("-1"));
			break;
		}

		return new RValue(resultExpression, resultCType);
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
		final String fullFunctionName = SFO.getBoogieFunctionName(smtFunctionName, new CPrimitive(floatType));
		final Expression result = ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
				new Expression[] { signBit, exponentBits, significantBits },
				mTypeHandler.getBoogieTypeForCType(new CPrimitive(floatType)));
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
					((TypeHandler) mTypeHandler).byteSize2AstType(loc, cprimitive.getPrimitiveCategory(), bytesize);
			final ASTType paramASTType = mTypeHandler.cType2AstType(loc, new CPrimitive(cprimitive));
			final ASTType[] params = new ASTType[] { paramASTType };
			final Attribute[] attributes =
					generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(), smtFunctionName, null);
			mFunctionDeclarations.declareFunction(loc, boogieFunctionName, attributes, bvType, params);
		}
		final Expression result = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
				new Expression[] { value }, mTypeHandler.getBoogieTypeForCType(new CPrimitive(cprimitive)));
		return result;
	}

	/**
	 * Declare a given list of binary bitvector functions for all integer datatypes. We use this as a workaround for the
	 * following problem. Usually, we only declare the bitvector functions that occur in the program. However, if an
	 * analysis constructs a proof in form of a Hoare annotation, this proof may also use other functions and our
	 * backtranslation crashes. 2017-05-03 Matthias: Currently it seems that it is sufficient to add only bvadd for all
	 * integer datatypes.
	 */
	@Override
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
