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
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.DeclarationResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
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
	protected static ITypeHandler mTypeHandler;
//	protected final IPointerIntegerConversion mPointerIntegerConversion;
	protected final FlatSymbolTable mSymboltable;

	protected final TranslationSettings mSettings;
	protected static int varCounter;

	public BitabsTranslation(final TypeSizes typeSizes, final TranslationSettings translationSettings,
			final ITypeHandler typeHandler, final FlatSymbolTable symboltable,
			FunctionDeclarations functionDeclarations) {
		mSettings = translationSettings;
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;
		mSymboltable = symboltable;
		mFunctionDeclarations = functionDeclarations;
		varCounter = 0;
	}

	public Expression abstractAnd(final ILocation loc, final int op, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		final String funcname = "bitwiseAnd";
		// if decides_to_apply(CYRUS_AND_0_LEFT, left, right)
		// If left is equal literal 0 or right is equal literal 0.
		Expression literal_0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		Expression literal_1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		Expression literal2 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "2");
		Expression left_eq1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left,
				literal_1);
		Expression left_eq0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left,
				literal_0);
		Expression right_eq1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right,
				literal_1);
		Expression right_eq0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right,
				literal_0);
		Expression leftUnsigned = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, left,
				literal_0);
		Expression rightUnsigned = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, right,
				literal_0);

		Expression left_size1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, left_eq1,
				left_eq0);
		Expression right_size1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
				right_eq1, right_eq0);
		
		Expression left_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, left,literal_0);
		Expression right_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, right,literal_0);

		/*
		 * Expression cond_left_1 = ExpressionFactory.newBinaryExpression(loc,
		 * BinaryExpression.Operator.LOGICAND, left_eq1, right_size1); Expression
		 * cond_right_1 =
		 * ExpressionFactory.newBinaryExpression(loc,BinaryExpression.Operator.LOGICAND,
		 * left_size1, right_eq1); Expression right_1_ite =
		 * ExpressionFactory.constructIfThenElseExpression(loc, cond_right_1, left,
		 * and_0); Expression and_abs =
		 * ExpressionFactory.constructIfThenElseExpression(loc, cond_left_1, right,
		 * right_1_ite);
		 */

		if (left instanceof IntegerLiteral) {
			String valueLeft = ((IntegerLiteral) left).getValue();
//			System.out.println("-----Light side constant value:" + valueLeft.equals("1"));
			if (valueLeft.equals("1")) {
				return right;
			} else if (valueLeft.equals("0")) {
				return left;
			}
		} else if (right instanceof IntegerLiteral) {
			String valueRight = ((IntegerLiteral) right).getValue();
			if (valueRight.equals("1")) {
				return left;
			} else if (valueRight.equals("0")) {
				return right;
			}

		} else if (isCompareOperator(left) && isCompareOperator(right)) {

			Expression left_neq0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, left,
					literal_0);
			Expression right_neq0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, right,
					literal_0);
			Expression logic_and = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
					left_neq0, right_neq0);
			//@CL For the type checking, bool to int, we need to constrcut the expression.
			Expression logic_ite = ExpressionFactory.constructIfThenElseExpression(loc, logic_and, literal_1, literal_0);
			
//			final ExpressionResult rl = exprResultTransformer.transformSwitchRexIntToBool(leftOperand, loc, hook);
//			final ExpressionResult rr = exprResultTransformer.transformSwitchRexIntToBool(rightOperand, loc, hook);
//			return handleAndOrOperators(loc, node.getOperator(), rl, rr);
			
			//@CL ultiamte compares all the expression result with 0 in final step for if condition!
			// So if the return type is bool, we need to set it back to int.
			//logic_and.setType(BoogiePrimitiveType.TYPE_INT);
			
			return logic_ite;
		}

		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;

		Expression cond_and_0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, left_eq0,
				right_eq0);
		Expression cond_and_1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, left_eq1,
				right_eq1);

		declareBitvectorFunction(loc, prefixedFunctionName, false, typeLeft, typeLeft, typeRight);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { left, right }, mTypeHandler.getBoogieTypeForCType(typeLeft));

		// a>0, a&1 <==> a%2
		Expression leftMod2 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMOD, left,
				literal2);
		Expression rightMod2 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMOD, right,
				literal2);
		// case a&0
//		Expression and_mod = ExpressionFactory.constructIfThenElseExpression(loc, right_eq1, leftMod2, func);
		Expression left_mod = ExpressionFactory.constructIfThenElseExpression(loc, left_pos, leftMod2, func);
		Expression right_mod = ExpressionFactory.constructIfThenElseExpression(loc, right_pos, rightMod2, func);
//		Expression and_pos = ExpressionFactory.constructIfThenElseExpression(loc, right_eq1, leftMod2, func);

		// for the case, a&1, if size(a) is not 1, the result would diverge, this is
		// actually equal to modular : -2&1=0, 2&1=0, 3&1=1.

		Expression condLeft1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, left_eq1,
				rightUnsigned);
		Expression condRight1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
				leftUnsigned, right_eq1);
//		Expression right_1_ite = ExpressionFactory.constructIfThenElseExpression(loc, condRight1, leftMod2, and_0);
//		Expression and_abs = ExpressionFactory.constructIfThenElseExpression(loc, condLeft1, rightMod2, right_1_ite);
//		Expression right_1_ite = ExpressionFactory.constructIfThenElseExpression(loc, left_eq1, rightMod2, and_mod);
	
		Expression right_bit_ite = ExpressionFactory.constructIfThenElseExpression(loc, right_size1, right, right_mod);
		
		Expression left_eq1_ite = ExpressionFactory.constructIfThenElseExpression(loc, left_eq1, right_bit_ite, func);
		
		Expression left_bit_ite = ExpressionFactory.constructIfThenElseExpression(loc, left_size1, left, left_mod);	
		Expression right_eq1_ite = ExpressionFactory.constructIfThenElseExpression(loc, right_eq1, left_bit_ite, left_eq1_ite);
		
		Expression and_abs = ExpressionFactory.constructIfThenElseExpression(loc, cond_and_0, literal_0, right_eq1_ite);
		return and_abs;
	}

	public Expression abstractOr(final ILocation loc, final int op, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		final String funcname = "bitwiseOr";
		if (left instanceof IntegerLiteral) {
			String valueLeft = ((IntegerLiteral) left).getValue();
			if (valueLeft.equals("1")) {
				return left;
			} else if (valueLeft.equals("0")) {
				return right;
			}
		} else if (right instanceof IntegerLiteral) {
			String valueRight = ((IntegerLiteral) right).getValue();
			if (valueRight.equals("1")) {
				return right;
			} else if (valueRight.equals("0")) {
				return left;
			}
		} 		
		
		Expression literal_1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		Expression literal_0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		Expression left_cmp1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left,
				literal_1);
		Expression left_cmp0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left,
				literal_0);
		Expression right_cmp1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right,
				literal_1);
		Expression right_cmp0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right,
				literal_0);

		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
		declareBitvectorFunction(loc, prefixedFunctionName, false, typeLeft, typeLeft, typeRight);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { left, right }, mTypeHandler.getBoogieTypeForCType(typeLeft));

		// bit-size(left/right) = 1 <==> (left/right == 1) || (left/right ==0)
		Expression left_size1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, left_cmp1,
				left_cmp0);
		Expression right_size1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
				right_cmp1, right_cmp0);
//		Expression left_right_size1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, left_size1, right_size1);

		// a|1 -> a
		Expression left_1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, left_cmp1, right_size1);
		Expression right_1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, left_size1,right_cmp1);
		Expression either_1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, left_1, right_1);
		
		// adding log_or rule here (a|b) == 0, when both operands are 0
		// Expression both_0 = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, left_cmp0, right_cmp0);		
		// Expression logic_or = ExpressionFactory.constructIfThenElseExpression(loc, both_0, literal_0, func);
		
		Expression or_1 = ExpressionFactory.constructIfThenElseExpression(loc, either_1, literal_1, func);

		// for the case, a|0 = a when a is bloolean or one bit size?
		Expression left_0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, left_cmp0, right_size1);
		Expression right_0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, left_size1, right_cmp0);

		Expression left_0_ite = ExpressionFactory.constructIfThenElseExpression(loc, left_0, right, or_1);
		Expression or_0 = ExpressionFactory.constructIfThenElseExpression(loc, right_0, left, left_0_ite);
		return or_0;
	}

	/**
	 * Construct right shift rules. In c for the gcc compiler with defualt settings,
	 * the a>>31 && a<0, return -1.
	 * 
	 **/

	public Expression abstractShiftRight(final ILocation loc, final int op, final Expression left,
			final CPrimitive typeLeft, final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		final String funcname = "shiftRight";
		Expression literal_0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		Expression literal_1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		Expression literal_31 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "31");
		Expression literal_63 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "63");

//		Expression left_cmp = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left,
//				literal_31);
		Expression right_cmp_31 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right,
				literal_31);
		Expression right_cmp_63 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right,
				literal_63);
		Expression right_cmp = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
				right_cmp_31, right_cmp_63);

		// left/right operand is positive and right/left operand is 31
		Expression left_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, left,
				literal_0);
//		Expression right_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, right,
//				literal_0);
		Expression left_cond_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
				left_pos, right_cmp);
//		Expression right_cond_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
//				left_cmp, right_pos);
//		Expression cond_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
//				left_cond_pos, right_cond_pos);

		if (right instanceof IntegerLiteral) {
			String valueRight = ((IntegerLiteral) right).getValue();
			if (valueRight.equals("31") || valueRight.equals("63")) {
				Expression signExpr = ExpressionFactory.constructIfThenElseExpression(loc, left_pos, literal_0,
						literal_1);
				return signExpr;
			}
		}

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
		Expression pos_ite = ExpressionFactory.constructIfThenElseExpression(loc, left_cond_pos, literal_0, func);

		// shiftRight on an negative number is unconventional, but according to the
		// evaluation from gcc compiler, a>>31 would results in -1
		Expression left_neg = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT, left,
				literal_0);
//		Expression right_neg = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT, right,
//				literal_0);
		Expression left_cond_neg = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
				left_neg, right_cmp);
//		Expression right_cond_neg = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
//				left_cmp, right_neg);
//		Expression cond_neg = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
//				left_cond_neg, right_cond_neg);

		Expression shiftRight = ExpressionFactory.constructIfThenElseExpression(loc, left_cond_neg, literal_1, pos_ite);
		return shiftRight;

	}

	/*
	 * solution: integer eqauls to 0 or 1, xor-1 rule
	 */
	public Expression abstractXor(final ILocation loc, final int op, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		final String funcname = "bitwiseXOr";

		Expression literal_1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		Expression literal_0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		Expression left_cmp1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left,
				literal_1);
		Expression left_cmp0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left,
				literal_0);

		Expression right_cmp1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right,
				literal_1);
		Expression right_cmp0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right,
				literal_0);
		Expression left_right_eq = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left,
				right);
		Expression left_right_neq = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, left,
				right);

		// bit-size(left/right) = 1 <==> (left/right == 1) || (left/right ==0), this is
		// not true when we represent integer in a fixed size bit-vector.
		Expression left_size1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, left_cmp1,
				left_cmp0);
		Expression right_size1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
				right_cmp1, right_cmp0);
		Expression left_right_size1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
				left_size1, right_size1);

		// Thinking about in binary world, when it comes to bit 0 or 1

		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
		declareBitvectorFunction(loc, prefixedFunctionName, false, typeLeft, typeLeft, typeRight);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { left, right }, mTypeHandler.getBoogieTypeForCType(typeLeft));

		// rule xor-0, for xor-1 rule, not stand, 0111 ^ 0001, negate doesn't work
		Expression right_ite_0 = ExpressionFactory.constructIfThenElseExpression(loc, right_cmp0, left, func);
		Expression left_ite_0 = ExpressionFactory.constructIfThenElseExpression(loc, left_cmp0, right, right_ite_0);
//		Expression cond_eq = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
//				left_right_size1, left_right_eq);
//		Expression cond_neq = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
//				left_right_size1, left_right_neq);
		
		Expression logic_xor = ExpressionFactory.constructIfThenElseExpression(loc, left_right_eq, literal_0, literal_1);
	
		
//		Expression xor_eq = ExpressionFactory.constructIfThenElseExpression(loc, cond_eq, literal_0, left_ite_0);
//		Expression xor = ExpressionFactory.constructIfThenElseExpression(loc, cond_neq, literal_1, xor_eq);
//		Expression xor_eq = ExpressionFactory.constructIfThenElseExpression(loc, cond_eq, literal_0, left_ite_0);
		Expression xor = ExpressionFactory.constructIfThenElseExpression(loc, left_right_size1, logic_xor, left_ite_0);
				
		return xor;
	}

	/*
	 * solution: integer eqauls to 0 or 1, complement-logic rule
	 */
	public Expression abstractCompl(final ILocation loc, final Expression expr, final CPrimitive type) {
		final String funcname = "bitwiseComplement";
		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
		declareBitvectorFunction(loc, prefixedFunctionName, false, type, type);

		if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) expr;
			Expression cond = ite.getCondition();
			Expression thenPart = ite.getThenPart();
			Expression elsePart = ite.getElsePart();
			// operand already translated into boogie
			return ExpressionFactory.constructIfThenElseExpression(loc, cond, elsePart, thenPart);

//			switch (ubin.getOperator()){
//			case COMPEQ:
//				return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, left, right);				
//			case COMPNEQ:	
//				return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, right);				
//			default: {
//				return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName, new Expression[] { expr },
//						mTypeHandler.getBoogieTypeForCType(type));
//				}
//			}
		} else {

			return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName, new Expression[] { expr },
					mTypeHandler.getBoogieTypeForCType(type));
		}
	}

	public static Result abstractAssgin(CHandler chandler, ProcedureManager mProcedureManager,
			ArrayList<Declaration> mDeclarations, ExpressionTranslation mExpressionTranslation,
			INameHandler mNameHandler, AuxVarInfoBuilder mAuxVarInfoBuilder, FlatSymbolTable symbolTable,
			ExpressionResultTransformer exprResultTransformer, IDispatcher main, LocationFactory locationFactory,
			IASTBinaryExpression node) {
		final ILocation loc = locationFactory.createCLocation(node);
		final ExpressionResult leftOperand = (ExpressionResult) main.dispatch(node.getOperand1());

		// this is an assignment expression, we won't need to translate it as before.
//		final ExpressionResult rightOperand = (ExpressionResult) main.dispatch(node.getOperand2());
		// We need to create a new id expression to store the expression here.
		// leftOperand we supposed to be an idExpression, implicit cast
		System.out.println("leftOperand expression: " + leftOperand.getLrValue().toString());
		LRValue left_Rvalue = leftOperand.getLrValue();
		IdentifierExpression id_left;
		if (left_Rvalue instanceof HeapLValue ) {
			id_left = (IdentifierExpression) ((HeapLValue)left_Rvalue).getAddress();
		} else {
			id_left = (IdentifierExpression) left_Rvalue.getValue();
		}
	//	IdentifierExpression id_left = (IdentifierExpression) ((RValue)leftOperand.getLrValue()).getValue();
		 			

		BoogieType bType = (BoogieType) id_left.getType();
		// Create the LRValue for the assignment statement.
		VariableLHS idLhs_left = new VariableLHS(loc, id_left.getType(), id_left.getIdentifier(),
				id_left.getDeclarationInformation());
//		LRValue idLhs_lrVal = new LocalLValue(idLhs_left, lType, false, false, null);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final CType lType = leftOperand.getLrValue().getCType().getUnderlyingType();
		Expression literal_1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		Expression literal_0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		// for declare the auxiliary vars.
//		varCounter++;
		if (node.getOperand2() instanceof IASTBinaryExpression) {
			// for the general bitwise assignment case, we build up assume statements.
			// System.out.println("----Is this binary expression contains bitwise operator?:
			// " + BitabsTranslation.containBitwise(node));

			IASTBinaryExpression rhs_bit = getBitwiseBinary((IASTBinaryExpression) node.getOperand2());
			boolean bit_op = BitabsTranslation.isBitwiseOperator(rhs_bit.getOperator());
//			System.out.println("----Is the binary operator a bitwise operator? " + bit_op);
			// make sure the bitiwse operator is right after the assignment operator in the
			// expression, if not, it would be treated as a normal binary expression.
			if (bit_op) {
				ExpressionResult rhs_opr1 = (ExpressionResult) main.dispatch(rhs_bit.getOperand1());
				ExpressionResult rhs_opr2 = (ExpressionResult) main.dispatch(rhs_bit.getOperand2());

				// array address expression, getValue() return exceptions.
				final ExpressionResult rl = exprResultTransformer
						.makeRepresentationReadyForConversionAndRexBoolToInt(rhs_opr1, loc, lType, node);
				final ExpressionResult rr = exprResultTransformer
						.makeRepresentationReadyForConversionAndRexBoolToInt(rhs_opr2, loc, lType, node);
				builder.addAllExceptLrValue(rl);
				builder.addAllExceptLrValue(rr);
				Expression opr1 = rl.getLrValue().getValue();
				Expression opr2 = rr.getLrValue().getValue();

				Expression opr1_eq0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, opr1,
						literal_0);
				Expression opr2_eq0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, opr2,
						literal_0);
				Expression opr1_eq1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, opr1,
						literal_1);
				Expression opr2_eq1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, opr2,
						literal_1);
				Expression opr1_bit = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
						opr1_eq0, opr1_eq1);
				Expression opr2_bit = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
						opr2_eq0, opr2_eq1);
				Expression cond_and_0 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
						opr1_eq0, opr2_eq0);

				Expression cond_rhs = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT, opr1,
						opr2);

				// Declare Global variable for assume abstraction, and, or general rules.
//				String bId = ("abs").concat(Integer.toString(varCounter));
				String bId = ("abs_").concat(Integer.toString(loc.getEndLine()));
				final ASTType astType = mTypeHandler.cType2AstType(loc, lType);
				DeclarationInformation decInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;
				final VariableDeclaration declVar = new VariableDeclaration(loc, new Attribute[0],
						new VarList[] { new VarList(loc, new String[] { bId }, astType) });
				// Declare a global variable, and register it to the global cope.
				mDeclarations.add(declVar);
				IdentifierExpression bit_var = ExpressionFactory.constructIdentifierExpression(loc, bType, bId,
						decInfo);
				final VariableLHS idLhs = ExpressionFactory.constructVariableLHS(loc, bType, bId, decInfo);

				if (rhs_bit.getOperator() == IASTBinaryExpression.op_binaryAnd) {

					Expression rhs_ite = ExpressionFactory.constructIfThenElseExpression(loc, cond_rhs, opr1, opr2);
//					Expression formula_left = ExpressionFactory.newBinaryExpression(loc,
//							BinaryExpression.Operator.COMPLT, leftOperand.getLrValue().getValue(), bit_var);
					Expression formula_left = ExpressionFactory.newBinaryExpression(loc,
							BinaryExpression.Operator.COMPLT, id_left, bit_var);
					
					IfStatement ifstmt_and = assumeIte(chandler, mProcedureManager, builder, lType, node, leftOperand,
							mNameHandler, mAuxVarInfoBuilder, symbolTable, exprResultTransformer,
							mExpressionTranslation, main, rhs_bit, opr1, opr2, rhs_ite, formula_left, idLhs);

					// add another if else nested statement statically to capture the bit-wise
					// operations in the stem position
					// and-1 rule condition
					Expression opr1_bit1 = ExpressionFactory.newBinaryExpression(loc,
							BinaryExpression.Operator.LOGICAND, opr1_eq1, opr2_bit);
					Expression opr2_bit1 = ExpressionFactory.newBinaryExpression(loc,
							BinaryExpression.Operator.LOGICAND, opr1_bit, opr2_eq1);

					final AssignmentStatement assignLiteral = StatementFactory.constructAssignmentStatement(loc,
							new LeftHandSide[] { idLhs_left }, new Expression[] { literal_0 });
					final AssignmentStatement assignOpr1 = StatementFactory.constructAssignmentStatement(loc,
							new LeftHandSide[] { idLhs_left }, new Expression[] { opr1 });
					final AssignmentStatement assignOpr2 = StatementFactory.constructAssignmentStatement(loc,
							new LeftHandSide[] { idLhs_left }, new Expression[] { opr2 });

					IfStatement ifstmt_opr1 = new IfStatement(loc, opr2_bit1, new Statement[] { assignOpr1 },
							new Statement[] { ifstmt_and });
					IfStatement ifstmt_opr2 = new IfStatement(loc, opr1_bit1, new Statement[] { assignOpr2 },
							new Statement[] { ifstmt_opr1 });
					IfStatement ifstmt1 = new IfStatement(loc, cond_and_0, new Statement[] { assignLiteral },
							new Statement[] { ifstmt_opr2 });
					builder.addStatement(ifstmt1);
					return builder.build();

				} else if (rhs_bit.getOperator() == IASTBinaryExpression.op_binaryOr) {
					Expression or_rhs_ite = ExpressionFactory.constructIfThenElseExpression(loc, cond_rhs, opr2, opr1);
					Expression or_formula_left = ExpressionFactory.newBinaryExpression(loc,
							BinaryExpression.Operator.COMPGEQ, leftOperand.getLrValue().getValue(), bit_var);

					IfStatement ifstmt_or = assumeIte(chandler, mProcedureManager, builder, lType, node, leftOperand,
							mNameHandler, mAuxVarInfoBuilder, symbolTable, exprResultTransformer,
							mExpressionTranslation, main, rhs_bit, opr1, opr2, or_rhs_ite, or_formula_left, idLhs);
					// add another if else nested statement statically to capture the bit-wise
					// operations in the stem position

					// or-0 rule condition
					Expression opr1_bit0 = ExpressionFactory.newBinaryExpression(loc,
							BinaryExpression.Operator.LOGICAND, opr1_eq0, opr2_bit);
					Expression opr2_bit0 = ExpressionFactory.newBinaryExpression(loc,
							BinaryExpression.Operator.LOGICAND, opr1_bit, opr2_eq0);
					// or-1 rule condition
					Expression opr1_bit1 = ExpressionFactory.newBinaryExpression(loc,
							BinaryExpression.Operator.LOGICAND, opr1_eq1, opr2_bit);
					Expression opr2_bit1 = ExpressionFactory.newBinaryExpression(loc,
							BinaryExpression.Operator.LOGICAND, opr1_bit, opr2_eq1);
					Expression cond_or1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
							opr1_bit1, opr2_bit1);

					final AssignmentStatement assignLiteral1 = StatementFactory.constructAssignmentStatement(loc,
							new LeftHandSide[] { idLhs_left }, new Expression[] { literal_1 });
					final AssignmentStatement assignOpr1 = StatementFactory.constructAssignmentStatement(loc,
							new LeftHandSide[] { idLhs_left }, new Expression[] { opr1 });
					final AssignmentStatement assignOpr2 = StatementFactory.constructAssignmentStatement(loc,
							new LeftHandSide[] { idLhs_left }, new Expression[] { opr2 });
					Expression condPos = ifstmt_or.getCondition();
					Statement[] thenPos = ifstmt_or.getThenPart();
					// nondet() assignment.
					Statement[] elsePos = ifstmt_or.getElsePart();

					IfStatement ifstmt_opr1 = new IfStatement(loc, opr2_bit0, new Statement[] { assignOpr1 },
							new Statement[] { ifstmt_or });
					IfStatement ifstmt_opr2 = new IfStatement(loc, opr1_bit0, new Statement[] { assignOpr2 },
							new Statement[] { ifstmt_opr1 });
					IfStatement ifstmt1 = new IfStatement(loc, cond_or1, new Statement[] { assignLiteral1 },
							new Statement[] { ifstmt_opr2 });
					// change the order to test result, general first
//
//					IfStatement ifstmt_literal = new IfStatement(loc, cond_or1, new Statement[] { assignLiteral1 }, elsePos);
//					IfStatement ifstmt_opr1 = new IfStatement(loc, opr2_bit0, new Statement[] { assignOpr1 }, new Statement[] { ifstmt_literal });
//					IfStatement ifstmt_opr2 = new IfStatement(loc, opr1_bit0, new Statement[] { assignOpr2 }, new Statement[] { ifstmt_opr1 });
//					IfStatement ifstmt1 = new IfStatement(loc, condPos, thenPos, new Statement[] { ifstmt_opr2 });	

					builder.addStatement(ifstmt1);
					return builder.build();

				} else if (rhs_bit.getOperator() == IASTBinaryExpression.op_binaryXor) {
					ExpressionResult xor_abs = (ExpressionResult) main.dispatch(rhs_bit);
					final ExpressionResultBuilder builder_xor = new ExpressionResultBuilder();
					builder_xor.addAllExceptLrValue(leftOperand);
					final ExpressionResult rightOperandSwitched = exprResultTransformer
							.makeRepresentationReadyForConversionAndRexBoolToInt(xor_abs, loc, lType, node);
					builder_xor.addAllIncludingLrValue(rightOperandSwitched);
					return chandler.makeAssignment(loc, leftOperand.getLrValue(), leftOperand.getNeighbourUnionFields(),
							builder_xor.build(), node);

				} else {
					throw new UnsupportedOperationException(
							"No general rules for bitiwse operator other than &, | in assume");
				}
			} else {
				// TODO, x = 1+x&(x-3)?
				throw new UnsupportedOperationException("ToDo, x = 1+x&(x-3)?...");
			}
		} else if (node.getOperand2() instanceof IASTUnaryExpression) {
			IASTUnaryExpression uIexpr = (IASTUnaryExpression) node.getOperand2();
			ExpressionResult uopr = (ExpressionResult) main.dispatch(uIexpr.getOperand());
			if (isBitwiseOperator(uIexpr.getOperator())) {

				Expression formula_neg = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
						leftOperand.getLrValue().getValue(), literal_0);
				Expression formula_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
						leftOperand.getLrValue().getValue(), literal_0);
				Expression com_pos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
						uopr.getLrValue().getValue(), literal_0);
				Expression com_neg = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
						uopr.getLrValue().getValue(), literal_0);

				AssumeStatement assume_then = new AssumeStatement(loc, formula_neg);
				AssumeStatement assume_else = new AssumeStatement(loc, formula_pos);
				// AssumeStatement assume_neg = new AssumeStatement(loc, com_neg);
//				IfStatement ifstmt1 = new IfStatement(loc, cond_or1, new Statement[] { assume_else }, new Statement[] { ifstmt1 });
				IfStatement ifstmt_com = new IfStatement(loc, com_pos, new Statement[] { assume_then },
						new Statement[] { assume_else });
				builder.addStatement(ifstmt_com);
				return builder.build();

			} else {
				// TODO, x = expr1 + ~expr2?
				throw new UnsupportedOperationException("ToDo, x = expr1 + ~expr2?...");
			}

		}
		return builder.build();
	}

	public static Result abstractRelational(CHandler chandler, ProcedureManager mProcedureManager,
			ArrayList<Declaration> mDeclarations, ExpressionTranslation mExpressionTranslation,
			INameHandler mNameHandler, AuxVarInfoBuilder mAuxVarInfoBuilder, FlatSymbolTable symbolTable,
			ExpressionResultTransformer exprResultTransformer, IDispatcher main, LocationFactory locationFactory,
			IASTBinaryExpression node) {

		final ILocation loc = locationFactory.createCLocation(node);
		final ExpressionResult leftOperand = (ExpressionResult) main.dispatch(node.getOperand1());
		final Expression left_val = leftOperand.getLrValue().getValue();
		final CType lType = leftOperand.getLrValue().getCType().getUnderlyingType();

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		Expression literal_0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		if (node.getOperand2() instanceof IASTBinaryExpression) {
			IASTBinaryExpression rhs_bit = getBitwiseBinary((IASTBinaryExpression) node.getOperand2());
			boolean bit_op = BitabsTranslation.isBitwiseOperator(rhs_bit.getOperator());

			// @CL make sure the bitiwse operator is right after the a relational operator
			// in the expression, if not, it would be treated as a normal integer binary
			// expression.
			if (bit_op) {
				ExpressionResult rhs_opr1 = (ExpressionResult) main.dispatch(rhs_bit.getOperand1());
				ExpressionResult rhs_opr2 = (ExpressionResult) main.dispatch(rhs_bit.getOperand2());

				// array address expression, getValue() return exceptions.
				final ExpressionResult rl = exprResultTransformer
						.makeRepresentationReadyForConversionAndRexBoolToInt(rhs_opr1, loc, lType, node);
				final ExpressionResult rr = exprResultTransformer
						.makeRepresentationReadyForConversionAndRexBoolToInt(rhs_opr2, loc, lType, node);
				builder.addAllExceptLrValue(rl);
				builder.addAllExceptLrValue(rr);
				Expression opr1 = rl.getLrValue().getValue();
				Expression opr2 = rr.getLrValue().getValue();

				Expression opr1_signed = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
						opr1, literal_0);
				Expression opr2_signed = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
						opr2, literal_0);
				Expression opr_signed = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
						opr1_signed, opr2_signed);

				if (rhs_bit.getOperator() == IASTBinaryExpression.op_binaryAnd) {
					final String funcname = "bitwiseAnd";
					final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
					final Expression func_and = ExpressionFactory.constructFunctionApplication(loc,
							prefixedFunctionName, new Expression[] { opr1, opr2 },
							mTypeHandler.getBoogieTypeForCType(lType));

					Expression left_opr1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
							left_val, opr1);
					Expression left_opr2 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
							left_val, opr2);
					Expression andLe = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
							left_opr1, left_opr2);

					Expression andElse = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
							left_val, func_and);
					Expression resultIte = ExpressionFactory.constructIfThenElseExpression(loc, opr_signed, andLe,
							andElse);
					final CPrimitive typeOfResult = new CPrimitive(CPrimitives.INT);
					final RValue rval = new RValue(resultIte, typeOfResult, true, false);
					builder.setLrValue(rval);
					return builder.build();

					/*
					 * } else if (rhs_bit.getOperator() == IASTBinaryExpression.op_binaryOr) {
					 * return builder.build();
					 */
				} else {
					throw new UnsupportedOperationException(
							"No general rules for bitiwse operator other than &, | in relational");
				}
			} else {
				// TODO, x = 1+x&(x-3)?
				throw new UnsupportedOperationException("ToDo, x = 1+x&(x-3)?...");
			}
		} else if (node.getOperand2() instanceof IASTUnaryExpression) {
			IASTUnaryExpression uIexpr = (IASTUnaryExpression) node.getOperand2();
			ExpressionResult uopr = (ExpressionResult) main.dispatch(uIexpr.getOperand());
			if (isBitwiseOperator(uIexpr.getOperator())) {

				return builder.build();

			} else {
				// TODO, x = expr1 + ~expr2?
				throw new UnsupportedOperationException("ToDo, x = expr1 + ~expr2?...");
			}

		}

		return builder.build();

	}

	/*
	 * method to make assume abstraction for genral bitwise and/or
	 * 
	 * @param bexpr
	 * 
	 */

	private static IfStatement assumeIte(CHandler chandler, ProcedureManager mProcedureManager,
			ExpressionResultBuilder builder, CType lType, IASTBinaryExpression node, ExpressionResult leftOperand,
			INameHandler mNameHandler, AuxVarInfoBuilder mAuxVarInfoBuilder, FlatSymbolTable symbolTable,
			ExpressionResultTransformer exprResultTransformer, ExpressionTranslation mExpressionTranslation,
			IDispatcher main, IASTBinaryExpression rhs_bit, Expression opr1, Expression opr2, Expression rhs_ite,
			Expression formula_left, VariableLHS idLhs) {
		// We need to create a new id expression to store the expression here.
		// leftOperand we supposed to be an idExpression, implicit cast
		IdentifierExpression id_left = (IdentifierExpression) leftOperand.getLrValue().getValue();
		ILocation loc = idLhs.getLoc();
//		BoogieType bType = (BoogieType) id_left.getType();
		// Create the LRValue for the assignment statement.
		VariableLHS idLhs_left = new VariableLHS(loc, id_left.getType(), id_left.getIdentifier(),
				id_left.getDeclarationInformation());
		LRValue idLhs_lrVal = new LocalLValue(idLhs_left, lType, false, false, null);

		Expression literal_0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		ExpressionResult rhs_opr1 = (ExpressionResult) main.dispatch(rhs_bit.getOperand1());
		ExpressionResult rhs_opr2 = (ExpressionResult) main.dispatch(rhs_bit.getOperand2());

		Expression opr1_signed = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, opr1,
				literal_0);
		Expression opr2_signed = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, opr2,
				literal_0);
		Expression opr_signed = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
				opr1_signed, opr2_signed);

		// for the elseStmt, we write it to an assignment with __VERRIFIER_nondet_int()
		// (nondet funciton) call
		String nondetName = "__VERRIFIER_nondet_int()";
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final AuxVarInfo auxvarinfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, lType, SFO.AUXVAR.NONDET);
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);

		final LRValue returnValue = new RValue(auxvarinfo.getExp(), lType);
		resultBuilder.setLrValue(returnValue);
		mExpressionTranslation.addAssumeValueInRangeStatements(loc, returnValue.getValue(), returnValue.getCType(),
				resultBuilder);
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, resultBuilder.getDeclarations(),
				resultBuilder.getAuxVars());
		ExpressionResult nondetResult = resultBuilder.build();
		final ExpressionResult nondetSwitched = exprResultTransformer
				.makeRepresentationReadyForConversionAndRexBoolToInt(nondetResult, loc, lType, node);
		ExpressionResult assignElse = chandler.makeAssignment(loc, idLhs_lrVal, leftOperand.getNeighbourUnionFields(),
				nondetSwitched, node);

		// We need to register this auxiliary variable, and this is local variable;
		// create the CDelaration for auxVar
		CDeclaration auxCdecl = new CDeclaration(lType, nondetName);
		DeclarationInformation auxDeclInfo = new DeclarationInformation(StorageClass.LOCAL,
				mProcedureManager.getCurrentProcedureID());
		SymbolTableValue aux_stv = new SymbolTableValue(auxvarinfo.getExp().getIdentifier(), auxvarinfo.getVarDec(),
				auxCdecl, auxDeclInfo, node, false);
		symbolTable.storeCSymbol(node, auxvarinfo.getExp().getIdentifier(), aux_stv);

		final ExpressionResult rightOperandSwitched = exprResultTransformer
				.makeRepresentationReadyForConversionAndRexBoolToInt(rhs_opr2, loc, lType, node);
		builder.addAllIncludingLrValue(rightOperandSwitched);

		AssumeStatement assume_pos = new AssumeStatement(loc, opr_signed);
		AssumeStatement assume_stmt = new AssumeStatement(loc, formula_left);
		final AssignmentStatement assignVal = StatementFactory.constructAssignmentStatement(loc,
				new LeftHandSide[] { idLhs }, new Expression[] { rhs_ite });

		final ArrayList<Statement> stmt = new ArrayList<>(assignElse.getStatements());
		final ArrayList<Declaration> decl = new ArrayList<>(assignElse.getDeclarations());
		final List<Overapprox> overappr = new ArrayList<>();

		stmt.addAll(CTranslationUtil.createHavocsForAuxVars(assignElse.getAuxVars()));
		overappr.addAll(assignElse.getOverapprs());
		ExpressionResult exprAssign = new ExpressionResult(stmt, assignElse.getLrValue(), decl, Collections.emptySet(),
				overappr);

		List<Statement> thenStmt = new ArrayList<>();
		List<Statement> elseStmt = new ArrayList<>(exprAssign.getStatements());
		thenStmt.add(assignVal);
		thenStmt.add(assume_pos);
		thenStmt.add(assume_stmt);
		IfStatement ifstmt = new IfStatement(loc, opr_signed, thenStmt.toArray(new Statement[thenStmt.size()]),
				elseStmt.toArray(new Statement[elseStmt.size()]));
		return ifstmt;

	}

	/*
	 * Utility methods
	 */

	/*
	 * method to decide if an expression has bitwise operator
	 * 
	 * @param bexpr for now we consider all binary cases, because the unary
	 * complement rule is not clear yet.
	 * 
	 */

	public static boolean containBitwise(final IASTExpression expr) {
		if (expr instanceof IASTBinaryExpression) {
			IASTBinaryExpression bexpr = (IASTBinaryExpression) expr;
			IASTExpression opr1 = bexpr.getOperand1();
			IASTExpression opr2 = bexpr.getOperand2();
			switch (bexpr.getOperator()) {
			case IASTBinaryExpression.op_binaryAnd:
			case IASTBinaryExpression.op_binaryAndAssign:
			case IASTBinaryExpression.op_binaryOr:
			case IASTBinaryExpression.op_binaryOrAssign:
			case IASTBinaryExpression.op_binaryXor:
			case IASTBinaryExpression.op_binaryXorAssign:
				return true;
			default: {
				if (opr1 instanceof IASTBinaryExpression)
					// No recursive here;
					// return containBitwise(opr1);
					return false;
				else if (opr2 instanceof IASTBinaryExpression)
					// return containBitwise(opr2);
					return false;
				else
					return false;
			}
			}
		} else if (expr instanceof IASTUnaryExpression) {
			IASTUnaryExpression uexpr = (IASTUnaryExpression) expr;
			IASTExpression opr = uexpr.getOperand();
			if (uexpr.getOperator() == IASTUnaryExpression.op_tilde) {
				return true;
			} else {
				// no recursive here;
				// return containBitwise(opr);
				return false;
			}
		} else {
			return false;
		}
	}

	// Justify if an operator is bitwise operator
	public static boolean isBitwiseOperator(int opcd) {

		switch (opcd) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryXorAssign:
		case IASTUnaryExpression.op_tilde:
			return true;
		default:
			return false;
		}
	}

	// Based on the heuristics ultimate translations on from comparison to ITE
	// expressions(an optimization from the Ultimate?)
	public static boolean isCompareOperator(Expression expr) {
		if (expr instanceof IfThenElseExpression) {
			return true;
		} else {
			return false;
		}
	}

	// Justify if an operator is bitwise operator we should return a list that
	// collect all the bit-wise expressions.
	public static IASTBinaryExpression getBitwiseBinary(IASTBinaryExpression binExpr) {
		int opcd = binExpr.getOperator();
		switch (opcd) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryXorAssign:
			return binExpr;
		default: {
			boolean left_bit = containBitwise(binExpr.getOperand1());
			boolean right_bit = containBitwise(binExpr.getOperand2());
			if (left_bit) {
				return getBitwiseBinary((IASTBinaryExpression) binExpr.getOperand1());
			} else if (right_bit) {
				return getBitwiseBinary((IASTBinaryExpression) binExpr.getOperand2());
			} else {
				throw new UnsupportedOperationException(
						"Neithter opertands of the %s contatins bitwise operation!" + binExpr.toString());
			}
		}
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
