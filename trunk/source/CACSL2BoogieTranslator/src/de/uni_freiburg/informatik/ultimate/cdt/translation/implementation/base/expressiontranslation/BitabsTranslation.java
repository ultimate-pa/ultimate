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
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UnsignedTreatment;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.SupportedBitvectorOperations;

/**
 *
 * @author Cyrus Liu
 *
 */
public class BitabsTranslation {

	public static final int STRING_OVERAPPROXIMATION_THRESHOLD = 8;

	protected final FunctionDeclarations mFunctionDeclarations;
	protected final TypeSizes mTypeSizes;
	protected final ITypeHandler mTypeHandler;
//	protected final IPointerIntegerConversion mPointerIntegerConversion;
	protected final FlatSymbolTable mSymboltable;

	protected final TranslationSettings mSettings;


	public BitabsTranslation(final TypeSizes typeSizes, final TranslationSettings translationSettings,
			final ITypeHandler typeHandler, final FlatSymbolTable symboltable, FunctionDeclarations functionDeclarations) {
		mSettings = translationSettings;
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;
		mSymboltable = symboltable;
		mFunctionDeclarations = functionDeclarations;
		}
	
	
	public Expression abstractAnd(final ILocation loc, final int op, final Expression left,
			final CPrimitive typeLeft, final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		final String funcname = "bitwiseAnd";	
		//if	decides_to_apply(CYRUS_AND_0_LEFT, left, right)
		if (left instanceof IntegerLiteral) {
			String valueLeft =((IntegerLiteral) left).getValue();
			System.out.println("-----Light side constant value:" + valueLeft.equals("1"));
			if (valueLeft.equals("1")) {
				return right;
				} else if (valueLeft.equals("0")){
					return left;
					} 
			} else if (right instanceof IntegerLiteral) {
				String valueRight = ((IntegerLiteral) right).getValue();
				System.out.println("-----Right side constant value:" + valueRight.equals("1"));
				if (valueRight.equals("1")) {
					return left;
					} else if (valueRight.equals("0")){
						return right;
						}
				} 
		Expression literal_0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		Expression left_cmp = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, literal_0);
		Expression right_cmp = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, literal_0);
		Expression cond_and_0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, left_cmp, right_cmp);
		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
		declareBitvectorFunction(loc, prefixedFunctionName, false, typeLeft, typeLeft, typeRight);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { left, right }, mTypeHandler.getBoogieTypeForCType(typeLeft));
		//	return func;
		// for the case, a&1 = a when a is bloolean or one bit size?
		// More case split results in nest if else expressions.
		Expression and_0 = ExpressionFactory.constructIfThenElseExpression(loc, cond_and_0, literal_0, func);
		return and_0;
		}
	
	public Expression abstractOr(final ILocation loc, final int op, final Expression left,
			final CPrimitive typeLeft, final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		final String funcname = "bitwiseOr";	
		if (left instanceof IntegerLiteral) {
			String valueLeft =((IntegerLiteral) left).getValue();
			if (valueLeft.equals("1")) {
				return left;
				} else if (valueLeft.equals("0")){
					return right;
					}
			} else if (right instanceof IntegerLiteral) {
				String valueRight = ((IntegerLiteral) right).getValue();
				if (valueRight.equals("1")) {
					return right;
					} else if (valueRight.equals("0")){
						return left;
						}
				}
		Expression literal_1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		Expression left_cmp = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, literal_1);
		Expression right_cmp = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, literal_1);
		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
		declareBitvectorFunction(loc, prefixedFunctionName, false, typeLeft, typeLeft, typeRight);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { left, right }, mTypeHandler.getBoogieTypeForCType(typeLeft));
		Expression right_ite = ExpressionFactory.constructIfThenElseExpression(loc, right_cmp, right, func);
		//	return func;
		// for the case, a|0 = a when a is bloolean or one bit size?
		Expression or_1 = ExpressionFactory.constructIfThenElseExpression(loc, left_cmp, left, right_ite);
		return or_1;			
	}
	
	
	/**
	 * Construct right shift rules.
	 * In c for the gcc compiler with defualt settings, the a>>31 && a<0, return -1.
	 * 
	 **/
	
	public Expression abstractShiftRight(final ILocation loc, final int op, final Expression left,
			final CPrimitive typeLeft, final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		final String funcname = "shiftRight";		
		Expression literal_0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		Expression literal_1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "-1");
	
		Expression literal_31 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "31");
		Expression left_cmp = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, literal_31);
		Expression right_cmp = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, literal_31);
		Expression left_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, left, literal_0);
		Expression right_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, right, literal_0);
		
		Expression left_cond_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, left_pos, right_cmp);
		Expression right_cond_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, left_cmp, right_pos);
		
		final BigInteger shiftRightLiteralValue = mTypeSizes.extractIntegerValue(right, typeRight, hook);
		Expression func;
		if (shiftRightLiteralValue != null) {
			func = constructShiftWithLiteralOptimization(loc, left, typeRight, shiftRightLiteralValue,
					Operator.ARITHDIV);
		} else {
			final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
			declareBitvectorFunction(loc, prefixedFunctionName, false, typeLeft, typeLeft, typeRight);
			func = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
					new Expression[] { left, right }, mTypeHandler.getBoogieTypeForCType(typeLeft));
			}
		Expression right_ite = ExpressionFactory.constructIfThenElseExpression(loc, right_cond_pos, literal_0, func);
		Expression shiftRight_pos = ExpressionFactory.constructIfThenElseExpression(loc, left_cond_pos, literal_0, right_ite);
		return shiftRight_pos;
			
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
		final Expression shiftFactorExpr = mTypeSizes.constructLiteralForIntegerType(loc, typeRight, shiftFactorBigInt);
		final Expression result = ExpressionFactory.newBinaryExpression(loc, op1, left, shiftFactorExpr);
		return result;
	}






}
