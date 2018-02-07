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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValueForArrays;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.StringLiteralResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3.FloatingPointLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;

public abstract class ExpressionTranslation {

	public static final int STRING_OVERAPPROXIMATION_THRESHOLD = 7;

	protected final FunctionDeclarations mFunctionDeclarations;
	protected final TypeSizes mTypeSizes;
	protected final ITypeHandler mTypeHandler;
	protected final IPointerIntegerConversion mPointerIntegerConversion;
	protected final boolean mOverapproximateFloatingPointOperations;

	public ExpressionTranslation(final TypeSizes typeSizes, final ITypeHandler typeHandler,
			final PointerIntegerConversion pointerIntegerConversion,
			final boolean overapproximateFloatingPointOperations) {
		super();
		mOverapproximateFloatingPointOperations = overapproximateFloatingPointOperations;
		mTypeSizes = typeSizes;
		mFunctionDeclarations = new FunctionDeclarations(typeHandler, mTypeSizes);
		mTypeHandler = typeHandler;
		switch (pointerIntegerConversion) {
		case IdentityAxiom:
			throw new UnsupportedOperationException("not yet implemented " + PointerIntegerConversion.IdentityAxiom);
		case NonBijectiveMapping:
			mPointerIntegerConversion = new NonBijectiveMapping(this, mTypeHandler);
			break;
		case NutzBijection:
			throw new UnsupportedOperationException("not yet implemented " + PointerIntegerConversion.NutzBijection);
		case Overapproximate:
			mPointerIntegerConversion = new OverapproximationUF(this, mFunctionDeclarations, mTypeHandler);
			break;
		default:
			throw new UnsupportedOperationException("unknown value " + pointerIntegerConversion);

		}
	}

	public ExpressionResult translateLiteral(final Dispatcher main, final IASTLiteralExpression node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_float_constant: {
			final String val = new String(node.getValue());
			final RValue rVal = translateFloatingLiteral(loc, val);
			assert rVal != null : "result must not be null";
			return new ExpressionResult(rVal);
		}
		case IASTLiteralExpression.lk_char_constant: {
			final BigInteger integerValue = ISOIEC9899TC3.handleCharConstant(new String(node.getValue()), loc, main);
			final CPrimitive charType = new CPrimitive(CPrimitives.CHAR);
			final Expression literal = constructLiteralForIntegerType(loc, charType, integerValue);
			return new ExpressionResult(new RValue(literal, charType));
		}
		case IASTLiteralExpression.lk_integer_constant: {
			final String val = new String(node.getValue());
			final RValue rVal = translateIntegerLiteral(loc, val);
			return new ExpressionResult(rVal);
		}
		case IASTLiteralExpression.lk_string_literal: {
			// subtract two from length for quotes at beginning and end
			final VariableDeclaration tVarDecl;
			final RValue rvalue;
			final String tId;
			{
				final int arrayLength = node.getValue().length - 2;
				final RValue dimension = new RValue(
						constructLiteralForIntegerType(loc, getCTypeOfPointerComponents(),
								BigInteger.valueOf(arrayLength)),
						getCTypeOfPointerComponents());
//				final RValue[] dimensions = { dimension };
//				final CArray arrayType = new CArray(dimensions, new CPrimitive(CPrimitives.CHAR));
				final CArray arrayType = new CArray(dimension, new CPrimitive(CPrimitives.CHAR));
				// final CPointer arrayType = new CPointer(new CPrimitive(CPrimitives.CHAR));
				tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.STRINGLITERAL, arrayType);
				tVarDecl = new VariableDeclaration(loc, new Attribute[0],
						new VarList[] { new VarList(loc, new String[] { tId }, mTypeHandler.constructPointerType(loc)) });
				rvalue = new RValueForArrays(new IdentifierExpression(loc, tId), arrayType);
			}
			final ArrayList<Declaration> decls = new ArrayList<>();
			decls.add(tVarDecl);
//			main.mCHandler.getStaticObjectsHandler().addGlobalDeclarations(decls);


			final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
			auxVars.put(tVarDecl, loc);

			/*
			 * construct a char[] that may be used for intitializing off-heap string variables.
			 */
			final char[] charArray;
			if (node.getValue().length >= 2 && node.getValue()[0] == '\"'
					&& node.getValue()[node.getValue().length - 1] == '\"') {
				charArray = Arrays.copyOfRange(node.getValue(), 1, node.getValue().length - 1);
			} else {
				throw new UnsupportedOperationException(
						"unsupported representation of string literal " + Arrays.toString(node.getValue()));
			}

			// overapproximate string literals of length STRING_OVERAPPROXIMATION_THRESHOLD or longer
			final boolean writeValues = charArray.length < STRING_OVERAPPROXIMATION_THRESHOLD;

			final List<Statement> statements =
					main.mCHandler.getMemoryHandler().writeStringToHeap(loc, tId, charArray, writeValues);
//			main.mCHandler.getStaticObjectsHandler().addStatementsForUltimateInit(statements);
//			main.mCHandler.getStaticObjectsHandler().addVariableModifiedByUltimateInit(tId);
//			main.mCHandler.getStaticObjectsHandler().addVariableModifiedByUltimateInit(SFO.VALID);
//			main.mCHandler.getStaticObjectsHandler().addVariableModifiedByUltimateInit(SFO.LENGTH);
//			if (writeValues) {
////				main.mCHandler.getStaticObjectsHandler().addVariableModifiedByUltimateInit(SFO.MEMORY_INT);
//				main.mCHandler.getStaticObjectsHandler().addVariableModifiedByUltimateInit(
//						main.mCHandler.getMemoryHandler().getMemoryModel().getDataHeapArray(CPrimitives.CHAR)
//							.getVariableName());
//			}

			final List<Overapprox> overapproxList;
			if (writeValues) {
				overapproxList = Collections.emptyList();
			} else {
				final Overapprox overapprox = new Overapprox("large string literal", loc);
				overapproxList = new ArrayList<>();
				overapproxList.add(overapprox);
			}
			return new StringLiteralResult(statements, rvalue, decls, auxVars, overapproxList,
					tId, charArray, !writeValues);
//			return new StringLiteralResult(Collections.emptyList(), rvalue, Collections.emptyList(),
//					Collections.emptyMap(), overapproxList, charArray);
		}
		case IASTLiteralExpression.lk_false:
			return new ExpressionResult(new RValue(new BooleanLiteral(loc, false), new CPrimitive(CPrimitives.INT)));
		case IASTLiteralExpression.lk_true:
			return new ExpressionResult(new RValue(new BooleanLiteral(loc, true), new CPrimitive(CPrimitives.INT)));
		default:
			final String msg = "Unknown or unsupported kind of IASTLiteralExpression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	public final Expression constructBinaryComparisonExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		// TODO: Check that types coincide
		if (type1.getGeneralType() == CPrimitiveCategory.FLOATTYPE
				|| type2.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			return constructBinaryComparisonFloatingPointExpression(loc, nodeOperator, exp1, type1, exp2, type2);
		}
		return constructBinaryComparisonIntegerExpression(loc, nodeOperator, exp1, type1, exp2, type2);
	}

	public final Expression constructBinaryBitwiseExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		// TODO: Check that types coincide
		if (type1.getGeneralType() == CPrimitiveCategory.FLOATTYPE
				|| type2.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(), "we do not support floats");
		}
		return constructBinaryBitwiseIntegerExpression(loc, nodeOperator, exp1, type1, exp2, type2);
	}

	public final Expression constructUnaryExpression(final ILocation loc, final int nodeOperator, final Expression exp,
			final CPrimitive type) {
		if (type.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			return constructUnaryFloatingPointExpression(loc, nodeOperator, exp, type);
		}
		return constructUnaryIntegerExpression(loc, nodeOperator, exp, type);
	}

	public final Expression constructArithmeticExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		// TODO: Check that types coincide
		if (type1.getGeneralType() == CPrimitiveCategory.FLOATTYPE
				|| type2.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			return constructArithmeticFloatingPointExpression(loc, nodeOperator, exp1, type1, exp2, type2);
		}
		return constructArithmeticIntegerExpression(loc, nodeOperator, exp1, type1, exp2, type2);
	}

	public abstract Expression constructBinaryComparisonIntegerExpression(ILocation loc, int nodeOperator,
			Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);

	public abstract Expression constructBinaryBitwiseIntegerExpression(ILocation loc, int nodeOperator, Expression exp1,
			CPrimitive type1, Expression exp2, CPrimitive type2);

	public abstract Expression constructUnaryIntegerExpression(ILocation loc, int nodeOperator, Expression exp,
			CPrimitive type);

	public abstract Expression constructArithmeticIntegerExpression(ILocation loc, int nodeOperator, Expression exp1,
			CPrimitive type1, Expression exp2, CPrimitive type2);

	public abstract Expression constructBinaryComparisonFloatingPointExpression(ILocation loc, int nodeOperator,
			Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);

	public abstract Expression constructUnaryFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp,
			CPrimitive type);

	public abstract Expression constructArithmeticFloatingPointExpression(ILocation loc, int nodeOperator,
			Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);

	public final Expression constructBinaryEqualityExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CType type1, final Expression exp2, final CType type2) {
		if (type1.isRealFloatingType() || type2.isRealFloatingType()) {
			return constructBinaryEqualityExpressionFloating(loc, nodeOperator, exp1, type1, exp2, type2);
		}
		return constructBinaryEqualityExpressionInteger(loc, nodeOperator, exp1, type1, exp2, type2);
	}

	public abstract Expression constructBinaryEqualityExpressionFloating(ILocation loc, int nodeOperator,
			Expression exp1, CType type1, Expression exp2, CType type2);

	public abstract Expression constructBinaryEqualityExpressionInteger(ILocation loc, int nodeOperator,
			Expression exp1, CType type1, Expression exp2, CType type2);

	public abstract RValue translateIntegerLiteral(ILocation loc, String val);

	public final RValue translateFloatingLiteral(final ILocation loc, final String val) {
		final FloatingPointLiteral fpl = ISOIEC9899TC3.handleFloatConstant(val, loc);
		final Expression expr =
				constructLiteralForFloatingType(loc, fpl.getCPrimitive(), fpl.getDecimalRepresenation());
		return new RValue(expr, fpl.getCPrimitive());
	}

	public abstract Expression constructLiteralForIntegerType(ILocation loc, CPrimitive type, BigInteger value);

	public abstract Expression constructLiteralForFloatingType(ILocation loc, CPrimitive type, BigDecimal value);

	public FunctionDeclarations getFunctionDeclarations() {
		return mFunctionDeclarations;
	}

	public CPrimitive determineResultOfUsualArithmeticConversions_Integer(final CPrimitive typeLeft,
			final CPrimitive typeRight) {

		if (typeLeft.equals(typeRight)) {
			return typeLeft;
		} else if ((mTypeSizes.isUnsigned(typeLeft) && mTypeSizes.isUnsigned(typeRight))
				|| (!mTypeSizes.isUnsigned(typeLeft) && !mTypeSizes.isUnsigned(typeRight))) {
			final Integer sizeLeft = mTypeSizes.getSize(typeLeft.getType());
			final Integer sizeRight = mTypeSizes.getSize(typeRight.getType());

			if (sizeLeft.compareTo(sizeRight) >= 0) {
				return typeLeft;
			}
			return typeRight;
		} else {
			CPrimitive unsignedType;
			CPrimitive signedType;

			if (mTypeSizes.isUnsigned(typeLeft)) {
				unsignedType = typeLeft;
				signedType = typeRight;
			} else {
				unsignedType = typeRight;
				signedType = typeLeft;
			}

			if (mTypeSizes.getSize(unsignedType.getType()).compareTo(mTypeSizes.getSize(signedType.getType())) >= 0) {
				return unsignedType;
			}
			return signedType;
		}
	}

	/**
	 * Apply usual arithmetic conversion according to 6.3.1.8 of the C11 standard. Therefore we determine the determine
	 * the CType of the result. Afterwards we convert both operands to the result CType.
	 *
	 * TODO: This is not correct for complex types. E.g., if double and complex float are operands, the complex float is
	 * converted to a complex double not to a (real double). Fixing this will be postponed until we want to support
	 * complex types.
	 */
	public void usualArithmeticConversions(final ILocation loc, final ExpressionResult leftRex,
			final ExpressionResult rightRex) {
		final CPrimitive leftPrimitive = (CPrimitive) CEnum.replaceEnumWithInt(leftRex.mLrVal.getCType());
		final CPrimitive rightPrimitive = (CPrimitive) CEnum.replaceEnumWithInt(leftRex.mLrVal.getCType());
		if (leftPrimitive.isIntegerType()) {
			doIntegerPromotion(loc, leftRex);
		}
		if (rightPrimitive.isIntegerType()) {
			doIntegerPromotion(loc, rightRex);
		}

		final CPrimitive resultType = determineResultOfUsualArithmeticConversions(
				(CPrimitive) leftRex.mLrVal.getCType(), (CPrimitive) rightRex.mLrVal.getCType());

		convertIfNecessary(loc, leftRex, resultType);
		convertIfNecessary(loc, rightRex, resultType);

		if (!leftRex.mLrVal.getCType().equals(resultType)) {
			throw new AssertionError("conversion failed");
		}
		if (!rightRex.mLrVal.getCType().equals(resultType)) {
			throw new AssertionError("conversion failed");
		}
	}

	/**
	 * Convert ResultExpression to resultType if its type is not already resultType.
	 */
	public void convertIfNecessary(final ILocation loc, final ExpressionResult operand, final CPrimitive resultType) {
		if (operand.mLrVal.getCType().equals(resultType)) {
			// do nothing
		} else {
			if (operand.mLrVal.getCType().isIntegerType()) {
				if (resultType.isIntegerType()) {
					convertIntToInt(loc, operand, resultType);
				} else if (resultType.isRealFloatingType()) {
					convertIntToFloat(loc, operand, resultType);
				} else {
					throw new UnsupportedSyntaxException(loc,
							"conversion from " + operand.mLrVal.getCType() + " to " + resultType);
				}
			} else if (operand.mLrVal.getCType().isRealFloatingType()) {
				if (resultType.isIntegerType()) {
					convertFloatToInt(loc, operand, resultType);
				} else if (resultType.isRealFloatingType()) {
					convertFloatToFloat(loc, operand, resultType);
				} else {
					throw new UnsupportedSyntaxException(loc,
							"conversion from " + operand.mLrVal.getCType() + " to " + resultType);
				}
			} else {
				throw new UnsupportedSyntaxException(loc,
						"conversion from " + operand.mLrVal.getCType() + " to " + resultType);
			}
		}
	}

	private CPrimitive determineResultOfUsualArithmeticConversions(final CPrimitive leftPrimitive,
			final CPrimitive rightPrimitive) {
		if (leftPrimitive.getGeneralType() == CPrimitiveCategory.FLOATTYPE
				|| rightPrimitive.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			if (leftPrimitive.getType() == CPrimitives.COMPLEX_LONGDOUBLE
					|| rightPrimitive.getType() == CPrimitives.COMPLEX_LONGDOUBLE) {
				throw new UnsupportedOperationException("complex types not yet supported");
			} else if (leftPrimitive.getType() == CPrimitives.COMPLEX_DOUBLE
					|| rightPrimitive.getType() == CPrimitives.COMPLEX_DOUBLE) {
				throw new UnsupportedOperationException("complex types not yet supported");
			} else if (leftPrimitive.getType() == CPrimitives.COMPLEX_FLOAT
					|| rightPrimitive.getType() == CPrimitives.COMPLEX_FLOAT) {
				throw new UnsupportedOperationException("complex types not yet supported");
			} else if (leftPrimitive.getType() == CPrimitives.LONGDOUBLE
					|| rightPrimitive.getType() == CPrimitives.LONGDOUBLE) {
				return new CPrimitive(CPrimitives.LONGDOUBLE);
			} else if (leftPrimitive.getType() == CPrimitives.DOUBLE
					|| rightPrimitive.getType() == CPrimitives.DOUBLE) {
				return new CPrimitive(CPrimitives.DOUBLE);
			} else if (leftPrimitive.getType() == CPrimitives.FLOAT || rightPrimitive.getType() == CPrimitives.FLOAT) {
				return new CPrimitive(CPrimitives.FLOAT);
			} else {
				throw new AssertionError("unknown FLOATTYPE " + leftPrimitive + ", " + rightPrimitive);
			}
		} else if (leftPrimitive.getGeneralType() == CPrimitiveCategory.INTTYPE
				&& rightPrimitive.getGeneralType() == CPrimitiveCategory.INTTYPE) {
			return determineResultOfUsualArithmeticConversions_Integer(leftPrimitive, rightPrimitive);
		} else {
			throw new AssertionError(
					"unsupported combination of CPrimitives: " + leftPrimitive + " and " + rightPrimitive);
		}
	}

	/**
	 * Conversion from some integer type to some integer type which is not _Bool.
	 */
	public abstract void convertIntToInt_NonBool(ILocation loc, ExpressionResult operand, CPrimitive resultType);

	public final void convertIntToInt(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		if (newType.getType() == CPrimitives.BOOL) {
			convertToBool(loc, rexp);
		} else {
			convertIntToInt_NonBool(loc, rexp, newType);
		}
	}

	/**
	 * Perform the integer promotions a specified in C11 6.3.1.1.2 on the operand.
	 */
	public final void doIntegerPromotion(final ILocation loc, final ExpressionResult operand) {
		final CType ctype = CEnum.replaceEnumWithInt(operand.mLrVal.getCType().getUnderlyingType());
		if (!(ctype instanceof CPrimitive)) {
			throw new IllegalArgumentException("integer promotions not applicable to " + ctype);
		}
		final CPrimitive cPrimitive = (CPrimitive) ctype;
		if (integerPromotionNeeded(cPrimitive)) {
			final CPrimitive promotedType = determineResultOfIntegerPromotion(cPrimitive);
			convertIntToInt(loc, operand, promotedType);
		}
	}

	private static boolean integerPromotionNeeded(final CPrimitive cPrimitive) {
		return (cPrimitive.getType().equals(CPrimitive.CPrimitives.CHAR) ||
		// cPrimitive.getType().equals(CPrimitive.PRIMITIVE.CHAR16) ||
		// cPrimitive.getType().equals(CPrimitive.PRIMITIVE.CHAR32) ||
				cPrimitive.getType().equals(CPrimitive.CPrimitives.SCHAR)
				|| cPrimitive.getType().equals(CPrimitive.CPrimitives.SHORT)
				|| cPrimitive.getType().equals(CPrimitive.CPrimitives.UCHAR) ||
				// cPrimitive.getType().equals(CPrimitive.PRIMITIVE.WCHAR) ||
				cPrimitive.getType().equals(CPrimitive.CPrimitives.USHORT));
	}

	/**
	 * Try to get the value of RValue rval. Returns null if extraction is impossible. Extraction might succeed if rval
	 * represents a constant value. Extraction fails, e.g., if rval represents a variable.
	 *
	 * @param expr
	 * @return
	 */
	public BigInteger extractIntegerValue(final RValue rval) {
		return extractIntegerValue(rval.getValue(), rval.getCType());
	}

	public abstract BigInteger extractIntegerValue(Expression expr, CType cType);

	private CPrimitive determineResultOfIntegerPromotion(final CPrimitive cPrimitive) {
		final int sizeOfArgument = mTypeSizes.getSize(cPrimitive.getType());
		final int sizeofInt = mTypeSizes.getSize(CPrimitive.CPrimitives.INT);

		if (sizeOfArgument < sizeofInt || !mTypeSizes.isUnsigned(cPrimitive)) {
			return new CPrimitive(CPrimitives.INT);
		}
		return new CPrimitive(CPrimitives.UINT);
	}

	/**
	 * In our Lindenmann-Hoenicke memory model, a pointer is a struct of two integer data types. This method returns the
	 * CType of the structs components.
	 */
	public abstract CPrimitive getCTypeOfPointerComponents();

	public final void convertPointerToInt(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		mPointerIntegerConversion.convertPointerToInt(loc, rexp, newType);
	}

	protected String declareConversionFunctionOverApprox(final ILocation loc, final CPrimitive oldType,
			final CPrimitive newType) {
		final String functionName = "convert" + oldType.toString() + "To" + newType.toString();
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
					new Expression[] { new StringLiteral(loc, functionName) });
			final Attribute[] attributes = new Attribute[] { attribute };
			final ASTType resultASTType = mTypeHandler.cType2AstType(loc, newType);
			final ASTType paramASTType = mTypeHandler.cType2AstType(loc, oldType);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultASTType, paramASTType);
		}
		return prefixedFunctionName;
	}

	abstract protected String declareConversionFunction(ILocation loc, CPrimitive oldType, CPrimitive newType);

	protected String declareBinaryFloatComparisonOverApprox(final ILocation loc, final CPrimitive type) {
		final String functionName = "someBinary" + type.toString() + "ComparisonOperation";
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
					new Expression[] { new StringLiteral(loc, functionName) });
			final Attribute[] attributes = new Attribute[] { attribute };
			final ASTType paramAstType = mTypeHandler.cType2AstType(loc, type);
			final ASTType resultAstType = new PrimitiveType(loc, SFO.BOOL);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultAstType, paramAstType,
					paramAstType);
		}
		return prefixedFunctionName;
	}

	private String declareBinaryArithmeticFloatOperation(final ILocation loc, final CPrimitive type) {
		final String functionName = "someBinaryArithmetic" + type.toString() + "operation";
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
					new Expression[] { new StringLiteral(loc, functionName) });
			final Attribute[] attributes = new Attribute[] { attribute };
			final ASTType astType = mTypeHandler.cType2AstType(loc, type);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType, astType, astType);
		}
		return prefixedFunctionName;
	}

	private String declareUnaryFloatOperation(final ILocation loc, final CPrimitive type) {
		final String functionName = "someUnary" + type.toString() + "operation";
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
					new Expression[] { new StringLiteral(loc, functionName) });
			final Attribute[] attributes = new Attribute[] { attribute };
			final ASTType astType = mTypeHandler.cType2AstType(loc, type);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType, astType);
		}
		return prefixedFunctionName;
	}

	public final void convertIntToPointer(final ILocation loc, final ExpressionResult rexp, final CPointer newType) {
		mPointerIntegerConversion.convertIntToPointer(loc, rexp, newType);
	}

	public void convertFloatToInt(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType) {
		if (newType.getType() == CPrimitives.BOOL) {
			convertToBool(loc, rexp);
		} else {
			convertFloatToInt_NonBool(loc, rexp, newType);
		}
	}

	public abstract void convertFloatToFloat(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType);

	public abstract void convertIntToFloat(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType);

	public abstract void convertFloatToInt_NonBool(ILocation loc, ExpressionResult rexp, CPrimitive newType);

	/**
	 * Convert any scalar type to _Bool. Section 6.3.1.2 of C11 says: When any scalar value is converted to _Bool, the
	 * result is 0 if the value compares equal to 0; otherwise, the result is 1.
	 */
	void convertToBool(final ILocation loc, final ExpressionResult rexp) {
		CType underlyingType = rexp.mLrVal.getCType();
		underlyingType = CEnum.replaceEnumWithInt(underlyingType);
		final Expression zeroInputType = constructZero(loc, underlyingType);
		final Expression isZero;
		if (underlyingType instanceof CPointer) {
			isZero = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ,
					rexp.mLrVal.getValue(), zeroInputType);
		} else if (underlyingType instanceof CPrimitive) {
			isZero = constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_equals, rexp.mLrVal.getValue(),
					(CPrimitive) underlyingType, zeroInputType, (CPrimitive) underlyingType);
		} else {
			throw new UnsupportedOperationException("unsupported: conversion from " + underlyingType + " to _Bool");
		}
		final Expression zeroBool =
				constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.BOOL), BigInteger.ZERO);
		final Expression oneBool =
				constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.BOOL), BigInteger.ONE);
		final Expression resultExpression = ExpressionFactory.newIfThenElseExpression(loc, isZero, zeroBool, oneBool);
		final RValue rValue = new RValue(resultExpression, new CPrimitive(CPrimitives.BOOL), false, false);
		rexp.mLrVal = rValue;
	}

	public abstract void addAssumeValueInRangeStatements(ILocation loc, Expression expr, CType ctype,
			List<Statement> stmt);

	public Expression constructNullPointer(final ILocation loc) {
		// return new IdentifierExpression(loc, SFO.NULL);
		return constructPointerForIntegerValues(loc, BigInteger.ZERO, BigInteger.ZERO);
	}

	public Expression constructPointerForIntegerValues(final ILocation loc, final BigInteger baseValue,
			final BigInteger offsetValue) {
		final Expression base = constructLiteralForIntegerType(loc, getCTypeOfPointerComponents(), baseValue);
		final Expression offset = constructLiteralForIntegerType(loc, getCTypeOfPointerComponents(), offsetValue);
		return MemoryHandler.constructPointerFromBaseAndOffset(base, offset, loc);
	}

	public Expression constructZero(final ILocation loc, final CType cType) {
		final Expression result;
		if (cType instanceof CPrimitive) {
			switch (((CPrimitive) cType).getGeneralType()) {
			case FLOATTYPE:
				result = constructLiteralForFloatingType(loc, (CPrimitive) cType, BigDecimal.ZERO);
				break;
			case INTTYPE:
				result = constructLiteralForIntegerType(loc, (CPrimitive) cType, BigInteger.ZERO);
				break;
			case VOID:
				throw new UnsupportedSyntaxException(loc, "no 0 value of type VOID");
			default:
				throw new AssertionError("illegal type");
			}
		} else if (cType instanceof CPointer) {
			result = constructNullPointer(loc);
		} else {
			throw new UnsupportedSyntaxException(loc, "don't know 0 value for type " + cType);
		}
		return result;
	}

	/**
	 * Returns an {@link Expression} that represents the following bits of operand high-1, high-2, ..., low+1, low
	 * (i.e., the bit at the higher index is not included, the bit at the lower index is included).
	 */
	public abstract Expression extractBits(ILocation loc, Expression operand, int high, int low);

	/**
	 * Presume that the input represents an integer that has inputWidth bit.
	 * Set all most significant bits to zero except the remainingWith least
	 * significant bits.
	 * I.e., the result is input representation that consists only of the bits.
	 * low-1, low-2, ..., 0
	 * If inputWidth and remainingWith are different the result is always positive.
	 */
	public abstract Expression erazeBits(ILocation loc, Expression value, CPrimitive cType, int remainingWith);

	public abstract Expression concatBits(ILocation loc, List<Expression> dataChunks, int size);

	public abstract Expression signExtend(ILocation loc, Expression operand, int bitsBefore, int bitsAfter);

	public abstract ExpressionResult createNanOrInfinity(ILocation loc, String name);

	public abstract Expression getRoundingMode();

	public abstract RValue constructOtherUnaryFloatOperation(ILocation loc, FloatFunction floatFunction,
			RValue argument);

	public abstract RValue constructOtherBinaryFloatOperation(ILocation loc, FloatFunction floatFunction, RValue first,
			RValue second);

	public Expression constructOverapproximationFloatLiteral(final ILocation loc, final String val,
			final CPrimitive type) {
		final String functionName = "floatingLiteral_" + makeBoogieIdentifierSuffix(val) + "_" + type;
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
					new Expression[] { new StringLiteral(loc, functionName) });
			final Attribute[] attributes = new Attribute[] { attribute };
			final ASTType astType = mTypeHandler.cType2AstType(loc, type);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType);
		}
		return new FunctionApplication(loc, prefixedFunctionName, new Expression[] {});

	}

	/**
	 * Translate string representation of a C literal to a string representation that is allowed in Boogie identifiers.
	 *
	 * @param val
	 *            string representation of C literal
	 * @return
	 */
	private static String makeBoogieIdentifierSuffix(final String val) {
		return val;
	}

	/**
	 * Check if id is number classification macro according to 7.12.6 of C11.
	 */
	public boolean isNumberClassificationMacro(final String cId) {
		return cId.equals("FP_NAN") || cId.equals("FP_INFINITE") || cId.equals("FP_ZERO") || cId.equals("FP_SUBNORMAL")
				|| cId.equals("FP_NORMAL");
	}

	/**
	 * Translate number classification macros according to 7.12.6 of C11. Although the standard allows any distinct
	 * integers, we take 0,1,2,3,4 because gcc on Matthias' Linux system uses these numbers.
	 */
	public RValue handleNumberClassificationMacro(final ILocation loc, final String cId) {
		final int number;
		switch (cId) {
		case "FP_NAN":
			number = 0;
			break;
		case "FP_INFINITE":
			number = 1;
			break;
		case "FP_ZERO":
			number = 2;
			break;
		case "FP_SUBNORMAL":
			number = 3;
			break;
		case "FP_NORMAL":
			number = 4;
			break;
		default:
			throw new IllegalArgumentException("no number classification macro " + cId);
		}
		final CPrimitive type = new CPrimitive(CPrimitives.INT);
		final Expression expr = constructLiteralForIntegerType(loc, type, BigInteger.valueOf(number));
		return new RValue(expr, type);
	}

	/**
	 * Generate the attributes for the Boogie code that make sure that we either - translate to the desired SMT
	 * functions, or - let Ultimate overapproximate
	 */
	protected Attribute[] generateAttributes(final ILocation loc, final boolean overapproximate,
			final String smtlibFunctionName, final int[] indices) {
		Attribute[] attributes;
		if (overapproximate) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
					new Expression[] { new StringLiteral(loc, smtlibFunctionName) });
			attributes = new Attribute[] { attribute };
		} else {
			if (indices == null) {
				final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
						new Expression[] { new StringLiteral(loc, smtlibFunctionName) });
				attributes = new Attribute[] { attribute };
			} else {
				final Expression[] literalIndices = new IntegerLiteral[indices.length];
				for (int i = 0; i < indices.length; ++i) {
					literalIndices[i] = new IntegerLiteral(loc, String.valueOf(indices[i]));
				}
				final Attribute attribute1 = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
						new Expression[] { new StringLiteral(loc, smtlibFunctionName) });
				final Attribute attribute2 =
						new NamedAttribute(loc, FunctionDeclarations.INDEX_IDENTIFIER, literalIndices);
				attributes = new Attribute[] { attribute1, attribute2 };
			}
		}
		return attributes;
	}

	public abstract Expression transformBitvectorToFloat(ILocation loc, Expression bitvector, CPrimitives floatType);

	public abstract Expression transformFloatToBitvector(ILocation loc, Expression value, CPrimitives cprimitive);



}
