/*
 * Copyright (C) 2021 Cyrus Liu (yliu195@stevens.edu)
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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 *
 * @author Cyrus Liu
 *
 */
public class BitabsTranslation {

	public static final int STRING_OVERAPPROXIMATION_THRESHOLD = 8;

	private final FunctionDeclarations mFunctionDeclarations;
	private final TypeSizes mTypeSizes;
	private final ITypeHandler mTypeHandler;
	private final FlatSymbolTable mSymboltable;

	public BitabsTranslation(final TypeSizes typeSizes, final ITypeHandler typeHandler,
			final FlatSymbolTable symboltable, final FunctionDeclarations functionDeclarations) {
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;
		mSymboltable = symboltable;
		mFunctionDeclarations = functionDeclarations;
	}

	public Expression abstractAnd(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight) {
		final String funcname = "bitwiseAnd";
		// if decides_to_apply(CYRUS_AND_0_LEFT, left, right)
		// If left is equal literal 0 or right is equal literal 0.
		final Expression lit0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		final Expression lit1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		final Expression lit2 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "2");
		final Expression leftEq1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, lit1);
		final Expression leftEq0 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, lit0);
		final Expression rightEq1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, lit1);
		final Expression rightEq0 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, lit0);

		final Expression leftSize1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, leftEq1, leftEq0);
		final Expression rightSize1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, rightEq1, rightEq0);

		final Expression leftPos =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, left, lit0);
		final Expression rightPos =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, right, lit0);

		if (left instanceof IntegerLiteral) {
			final String valueLeft = ((IntegerLiteral) left).getValue();
			if (valueLeft.equals("1")) {
				return right;
			}
			if (valueLeft.equals("0")) {
				return left;
			}
		} else if (right instanceof IntegerLiteral) {
			final String valueRight = ((IntegerLiteral) right).getValue();
			if (valueRight.equals("1")) {
				return left;
			}
			if (valueRight.equals("0")) {
				return right;
			}

		} else if (isCompareOperator(left) && isCompareOperator(right)) {

			final Expression leftNeq0 =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, left, lit0);
			final Expression rightNeq0 =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, right, lit0);
			final Expression logicAnd =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leftNeq0, rightNeq0);

			// Ultimate compares all the expression result with 0 in final step for if //
			// condition! So if the return type is bool, we need to set it back to int.
			return ExpressionFactory.constructIfThenElseExpression(loc, logicAnd, lit1, lit0);
		}

		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;

		final Expression condAnd0 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, leftEq0, rightEq0);

		declareBitvectorFunction(loc, prefixedFunctionName, false, typeLeft, typeLeft, typeRight);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { left, right }, mTypeHandler.getBoogieTypeForCType(typeLeft));

		// a>0, a&1 <==> a%2
		final Expression leftMod2 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMOD, left, lit2);
		final Expression rightMod2 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMOD, right, lit2);
		// case a&0
		final Expression leftMod = ExpressionFactory.constructIfThenElseExpression(loc, leftPos, leftMod2, func);
		final Expression rightMod = ExpressionFactory.constructIfThenElseExpression(loc, rightPos, rightMod2, func);

		// for the case, a&1, if size(a) is not 1, the result would diverge, this is
		// actually equal to modular : -2&1=0, 2&1=0, 3&1=1.

		final Expression rightBitIte =
				ExpressionFactory.constructIfThenElseExpression(loc, rightSize1, right, rightMod);

		final Expression leftEq1Ite = ExpressionFactory.constructIfThenElseExpression(loc, leftEq1, rightBitIte, func);

		final Expression leftBitIte = ExpressionFactory.constructIfThenElseExpression(loc, leftSize1, left, leftMod);
		final Expression rightEq1Ite =
				ExpressionFactory.constructIfThenElseExpression(loc, rightEq1, leftBitIte, leftEq1Ite);

		return ExpressionFactory.constructIfThenElseExpression(loc, condAnd0, lit0, rightEq1Ite);
	}

	public Expression abstractOr(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight) {
		final String funcname = "bitwiseOr";
		if (left instanceof IntegerLiteral) {
			final String valueLeft = ((IntegerLiteral) left).getValue();
			if (valueLeft.equals("1")) {
				return left;
			}
			if (valueLeft.equals("0")) {
				return right;
			}
		} else if (right instanceof IntegerLiteral) {
			final String valueRight = ((IntegerLiteral) right).getValue();
			if (valueRight.equals("1")) {
				return right;
			}
			if (valueRight.equals("0")) {
				return left;
			}
		}

		final Expression lit1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		final Expression lit0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		final Expression leftCmp1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, lit1);
		final Expression leftCmp0 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, lit0);
		final Expression rightCmp1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, lit1);
		final Expression rightCmp0 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, lit0);

		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
		declareBitvectorFunction(loc, prefixedFunctionName, false, typeLeft, typeLeft, typeRight);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { left, right }, mTypeHandler.getBoogieTypeForCType(typeLeft));

		// bit-size(left/right) = 1 <==> (left/right == 1) || (left/right ==0)
		final Expression leftSize1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, leftCmp1, leftCmp0);
		final Expression rightSize1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, rightCmp1, rightCmp0);

		// a|1 -> a
		final Expression left1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leftCmp1, rightSize1);
		final Expression right1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leftSize1, rightCmp1);
		final Expression either1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, left1, right1);

		// adding log_or rule here (a|b) == 0, when both operands are 0
		final Expression or1 = ExpressionFactory.constructIfThenElseExpression(loc, either1, lit1, func);

		// for the case, a|0 = a when a is bloolean or one bit size?
		final Expression left0 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leftCmp0, rightSize1);
		final Expression right0 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leftSize1, rightCmp0);

		final Expression left0Ite = ExpressionFactory.constructIfThenElseExpression(loc, left0, right, or1);
		return ExpressionFactory.constructIfThenElseExpression(loc, right0, left, left0Ite);
	}

	/**
	 * Construct right shift rules. In c for the gcc compiler with defualt settings, the a>>31 && a<0, return -1.
	 * 
	 **/

	public Expression abstractShiftRight(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		final String funcname = "shiftRight";
		final Expression lit0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		final Expression lit1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		final Expression lit31 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "31");
		final Expression lit63 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "63");

		final Expression rightCmp31 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, lit31);
		final Expression rightCmp63 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, lit63);
		final Expression rightCmp =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, rightCmp31, rightCmp63);

		// left/right operand is positive and right/left operand is 31
		final Expression leftPos =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, left, lit0);
		final Expression leftCondPos =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leftPos, rightCmp);

		if (right instanceof IntegerLiteral) {
			final String valueRight = ((IntegerLiteral) right).getValue();
			if (valueRight.equals("31") || valueRight.equals("63")) {
				return ExpressionFactory.constructIfThenElseExpression(loc, leftPos, lit0, lit1);
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
		final Expression posIte = ExpressionFactory.constructIfThenElseExpression(loc, leftCondPos, lit0, func);

		// shiftRight on an negative number is unconventional, but according to the
		// evaluation from gcc compiler, a>>31 would results in -1
		final Expression leftNeg =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT, left, lit0);
		final Expression leftCondNeg =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leftNeg, rightCmp);

		return ExpressionFactory.constructIfThenElseExpression(loc, leftCondNeg, lit1, posIte);

	}

	/*
	 * solution: integer eqauls to 0 or 1, xor-1 rule
	 */
	public Expression abstractXor(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight) {
		final String funcname = "bitwiseXOr";

		final Expression lit1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		final Expression lit0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		final Expression leftCmp1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, lit1);
		final Expression leftCmp0 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, lit0);

		final Expression rightCmp1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, lit1);
		final Expression rightCmp0 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, right, lit0);
		final Expression leftRightEq =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, left, right);

		// bit-size(left/right) = 1 <==> (left/right == 1) || (left/right ==0), this is
		// not true when we represent integer in a fixed size bit-vector.
		final Expression leftSize1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, leftCmp1, leftCmp0);
		final Expression rightSize1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, rightCmp1, rightCmp0);
		final Expression leftRightSize1 =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leftSize1, rightSize1);

		// Thinking about in binary world, when it comes to bit 0 or 1

		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
		declareBitvectorFunction(loc, prefixedFunctionName, false, typeLeft, typeLeft, typeRight);
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { left, right }, mTypeHandler.getBoogieTypeForCType(typeLeft));

		// rule xor-0, for xor-1 rule, not stand, 0111 ^ 0001, negate doesn't work
		final Expression rightIte0 = ExpressionFactory.constructIfThenElseExpression(loc, rightCmp0, left, func);
		final Expression leftIte0 = ExpressionFactory.constructIfThenElseExpression(loc, leftCmp0, right, rightIte0);

		final Expression logicXor = ExpressionFactory.constructIfThenElseExpression(loc, leftRightEq, lit0, lit1);

		return ExpressionFactory.constructIfThenElseExpression(loc, leftRightSize1, logicXor, leftIte0);
	}

	/*
	 * solution: integer eqauls to 0 or 1, complement-logic rule
	 */
	public Expression abstractCompl(final ILocation loc, final Expression expr, final CPrimitive type) {
		final String funcname = "bitwiseComplement";
		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
		declareBitvectorFunction(loc, prefixedFunctionName, false, type, type);

		if (expr instanceof IfThenElseExpression) {
			final IfThenElseExpression ite = (IfThenElseExpression) expr;
			final Expression cond = ite.getCondition();
			final Expression thenPart = ite.getThenPart();
			final Expression elsePart = ite.getElsePart();
			// operand already translated into boogie
			return ExpressionFactory.constructIfThenElseExpression(loc, cond, elsePart, thenPart);

		}
		return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName, new Expression[] { expr },
				mTypeHandler.getBoogieTypeForCType(type));
	}

	public Result abstractAssign(final CHandler chandler, final ProcedureManager procedureManager,
			final List<Declaration> declarations, final ExpressionTranslation expressionTranslation,
			final INameHandler nameHandler, final AuxVarInfoBuilder auxVarInfoBuilder,
			final ExpressionResultTransformer exprResultTransformer, final IDispatcher main,
			final LocationFactory locationFactory, final IASTBinaryExpression node) {
		final ILocation loc = locationFactory.createCLocation(node);
		final ExpressionResult leftOperand = (ExpressionResult) main.dispatch(node.getOperand1());

		// this is an assignment expression, we won't need to translate it as before.
		// We need to create a new id expression to store the expression here.
		// leftOperand we supposed to be an idExpression, implicit cast
		final LRValue leftRvalue = leftOperand.getLrValue();
		final IdentifierExpression idLeft;
		if (leftRvalue instanceof HeapLValue) {
			idLeft = (IdentifierExpression) ((HeapLValue) leftRvalue).getAddress();
		} else {
			idLeft = (IdentifierExpression) leftRvalue.getValue();
		}

		final BoogieType bType = (BoogieType) idLeft.getType();
		// Create the LRValue for the assignment statement.
		final VariableLHS idLhsLeft =
				new VariableLHS(loc, idLeft.getType(), idLeft.getIdentifier(), idLeft.getDeclarationInformation());

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final CType lType = leftOperand.getLrValue().getCType().getUnderlyingType();
		final Expression lit1 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "1");
		final Expression lit0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		// for declare the auxiliary vars.
		if (node.getOperand2() instanceof IASTBinaryExpression) {
			// for the general bitwise assignment case, we build up assume statements.

			final IASTBinaryExpression rhsBit = getBitwiseBinary((IASTBinaryExpression) node.getOperand2());
			final boolean bitOp = BitabsTranslation.isBitwiseOperator(rhsBit.getOperator());
			// make sure the bitiwse operator is right after the assignment operator in the
			// expression, if not, it would be treated as a normal binary expression.
			if (!bitOp) {
				// TODO, x = 1+x&(x-3)?
				throw new UnsupportedOperationException("ToDo, x = 1+x&(x-3)?...");
			}
			final ExpressionResult rhsOpr1 = (ExpressionResult) main.dispatch(rhsBit.getOperand1());
			final ExpressionResult rhsOpr2 = (ExpressionResult) main.dispatch(rhsBit.getOperand2());

			// array address expression, getValue() return exceptions.
			final ExpressionResult rl = exprResultTransformer
					.makeRepresentationReadyForConversionAndRexBoolToInt(rhsOpr1, loc, lType, node);
			final ExpressionResult rr = exprResultTransformer
					.makeRepresentationReadyForConversionAndRexBoolToInt(rhsOpr2, loc, lType, node);
			builder.addAllExceptLrValue(rl);
			builder.addAllExceptLrValue(rr);
			final Expression opr1 = rl.getLrValue().getValue();
			final Expression opr2 = rr.getLrValue().getValue();

			final Expression opr1Eq0 =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, opr1, lit0);
			final Expression opr2Eq0 =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, opr2, lit0);
			final Expression opr1Eq1 =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, opr1, lit1);
			final Expression opr2Eq1 =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, opr2, lit1);
			final Expression opr1Bit =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, opr1Eq0, opr1Eq1);
			final Expression opr2Bit =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, opr2Eq0, opr2Eq1);
			final Expression condAnd0 =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR, opr1Eq0, opr2Eq0);
			final Expression condRhs =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT, opr1, opr2);

			// Declare Global variable for assume abstraction, and, or general rules.
			final String bId = "abs_".concat(Integer.toString(loc.getEndLine()));
			final ASTType astType = mTypeHandler.cType2AstType(loc, lType);
			final DeclarationInformation decInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;
			final VariableDeclaration declVar = new VariableDeclaration(loc, new Attribute[0],
					new VarList[] { new VarList(loc, new String[] { bId }, astType) });
			// Declare a global variable, and register it to the global cope.
			declarations.add(declVar);
			final IdentifierExpression bitVar =
					ExpressionFactory.constructIdentifierExpression(loc, bType, bId, decInfo);
			final VariableLHS idLhs = ExpressionFactory.constructVariableLHS(loc, bType, bId, decInfo);

			if (rhsBit.getOperator() == IASTBinaryExpression.op_binaryAnd) {

				final Expression rhsIte = ExpressionFactory.constructIfThenElseExpression(loc, condRhs, opr1, opr2);
				final Expression formulaLeft =
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT, idLeft, bitVar);

				final IfStatement ifstmtAnd = assumeIte(chandler, procedureManager, builder, lType, node, leftOperand,
						nameHandler, auxVarInfoBuilder, mSymboltable, exprResultTransformer, expressionTranslation,
						main, rhsBit, opr1, opr2, rhsIte, formulaLeft, idLhs);

				// add another if else nested statement statically to capture the bit-wise
				// operations in the stem position
				// and-1 rule condition
				final Expression opr1Bit1 = ExpressionFactory.newBinaryExpression(loc,
						BinaryExpression.Operator.LOGICAND, opr1Eq1, opr2Bit);
				final Expression opr2Bit1 = ExpressionFactory.newBinaryExpression(loc,
						BinaryExpression.Operator.LOGICAND, opr1Bit, opr2Eq1);

				final AssignmentStatement assignLiteral = StatementFactory.constructAssignmentStatement(loc,
						new LeftHandSide[] { idLhsLeft }, new Expression[] { lit0 });
				final AssignmentStatement assignOpr1 = StatementFactory.constructAssignmentStatement(loc,
						new LeftHandSide[] { idLhsLeft }, new Expression[] { opr1 });
				final AssignmentStatement assignOpr2 = StatementFactory.constructAssignmentStatement(loc,
						new LeftHandSide[] { idLhsLeft }, new Expression[] { opr2 });

				final IfStatement ifstmtOpr1 =
						new IfStatement(loc, opr2Bit1, new Statement[] { assignOpr1 }, new Statement[] { ifstmtAnd });
				final IfStatement ifstmtOpr2 =
						new IfStatement(loc, opr1Bit1, new Statement[] { assignOpr2 }, new Statement[] { ifstmtOpr1 });
				final IfStatement ifstmt1 = new IfStatement(loc, condAnd0, new Statement[] { assignLiteral },
						new Statement[] { ifstmtOpr2 });
				builder.addStatement(ifstmt1);
				return builder.build();

			}
			if (rhsBit.getOperator() == IASTBinaryExpression.op_binaryOr) {
				final Expression orRhsIte = ExpressionFactory.constructIfThenElseExpression(loc, condRhs, opr2, opr1);
				final Expression orFormulaLeft = ExpressionFactory.newBinaryExpression(loc,
						BinaryExpression.Operator.COMPGEQ, leftOperand.getLrValue().getValue(), bitVar);

				final IfStatement ifstmtOr = assumeIte(chandler, procedureManager, builder, lType, node, leftOperand,
						nameHandler, auxVarInfoBuilder, mSymboltable, exprResultTransformer, expressionTranslation,
						main, rhsBit, opr1, opr2, orRhsIte, orFormulaLeft, idLhs);
				// add another if else nested statement statically to capture the bit-wise
				// operations in the stem position

				// or-0 rule condition
				final Expression opr1Bit0 = ExpressionFactory.newBinaryExpression(loc,
						BinaryExpression.Operator.LOGICAND, opr1Eq0, opr2Bit);
				final Expression opr2Bit0 = ExpressionFactory.newBinaryExpression(loc,
						BinaryExpression.Operator.LOGICAND, opr1Bit, opr2Eq0);
				// or-1 rule condition
				final Expression opr1Bit1 = ExpressionFactory.newBinaryExpression(loc,
						BinaryExpression.Operator.LOGICAND, opr1Eq1, opr2Bit);
				final Expression opr2Bit1 = ExpressionFactory.newBinaryExpression(loc,
						BinaryExpression.Operator.LOGICAND, opr1Bit, opr2Eq1);
				final Expression condOr1 = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
						opr1Bit1, opr2Bit1);

				final AssignmentStatement assignLiteral1 = StatementFactory.constructAssignmentStatement(loc,
						new LeftHandSide[] { idLhsLeft }, new Expression[] { lit1 });
				final AssignmentStatement assignOpr1 = StatementFactory.constructAssignmentStatement(loc,
						new LeftHandSide[] { idLhsLeft }, new Expression[] { opr1 });
				final AssignmentStatement assignOpr2 = StatementFactory.constructAssignmentStatement(loc,
						new LeftHandSide[] { idLhsLeft }, new Expression[] { opr2 });
				// nondet() assignment.
				final IfStatement ifstmtOpr1 =
						new IfStatement(loc, opr2Bit0, new Statement[] { assignOpr1 }, new Statement[] { ifstmtOr });
				final IfStatement ifstmtOpr2 =
						new IfStatement(loc, opr1Bit0, new Statement[] { assignOpr2 }, new Statement[] { ifstmtOpr1 });
				final IfStatement ifstmt1 = new IfStatement(loc, condOr1, new Statement[] { assignLiteral1 },
						new Statement[] { ifstmtOpr2 });
				// change the order to test result, general first
				builder.addStatement(ifstmt1);
				return builder.build();

			}
			if (rhsBit.getOperator() == IASTBinaryExpression.op_binaryXor) {
				final ExpressionResult xorAbs = (ExpressionResult) main.dispatch(rhsBit);
				final ExpressionResultBuilder builderXor = new ExpressionResultBuilder();
				builderXor.addAllExceptLrValue(leftOperand);
				final ExpressionResult rightOperandSwitched = exprResultTransformer
						.makeRepresentationReadyForConversionAndRexBoolToInt(xorAbs, loc, lType, node);
				builderXor.addAllIncludingLrValue(rightOperandSwitched);
				return chandler.makeAssignment(loc, leftOperand.getLrValue(), leftOperand.getNeighbourUnionFields(),
						builderXor.build(), node);

			}
			throw new UnsupportedOperationException("No general rules for bitiwse operator other than &, | in assume");
		}
		if (node.getOperand2() instanceof IASTUnaryExpression) {
			final IASTUnaryExpression uIexpr = (IASTUnaryExpression) node.getOperand2();
			final ExpressionResult uopr = (ExpressionResult) main.dispatch(uIexpr.getOperand());
			if (!isBitwiseOperator(uIexpr.getOperator())) {
				// TODO, x = expr1 + ~expr2?
				throw new UnsupportedOperationException("ToDo, x = expr1 + ~expr2?...");
			}
			final Expression formulaNeg = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT,
					leftOperand.getLrValue().getValue(), lit0);
			final Expression formulaPos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
					leftOperand.getLrValue().getValue(), lit0);
			final Expression comPos = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
					uopr.getLrValue().getValue(), lit0);

			final AssumeStatement assumeThen = new AssumeStatement(loc, formulaNeg);
			final AssumeStatement assumeElse = new AssumeStatement(loc, formulaPos);
			final IfStatement ifstmtCom =
					new IfStatement(loc, comPos, new Statement[] { assumeThen }, new Statement[] { assumeElse });
			builder.addStatement(ifstmtCom);

		}
		return builder.build();
	}

	public Result abstractRelational(final ExpressionResultTransformer exprResultTransformer, final IDispatcher main,
			final LocationFactory locationFactory, final IASTBinaryExpression node) {

		final ILocation loc = locationFactory.createCLocation(node);
		final ExpressionResult leftOperand = (ExpressionResult) main.dispatch(node.getOperand1());
		final Expression leftVal = leftOperand.getLrValue().getValue();
		final CType lType = leftOperand.getLrValue().getCType().getUnderlyingType();

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final Expression lit0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		if (node.getOperand2() instanceof IASTBinaryExpression) {
			final IASTBinaryExpression rhsBit = getBitwiseBinary((IASTBinaryExpression) node.getOperand2());
			final boolean bitOp = BitabsTranslation.isBitwiseOperator(rhsBit.getOperator());

			// make sure the bitiwse operator is right after the a relational operator in the expression, if not, it
			// would be treated as a normal integer binary expression.
			if (!bitOp) {
				// TODO, x = 1+x&(x-3)?
				throw new UnsupportedOperationException("ToDo, x = 1+x&(x-3)?...");
			}
			final ExpressionResult rhsOpr1 = (ExpressionResult) main.dispatch(rhsBit.getOperand1());
			final ExpressionResult rhsOpr2 = (ExpressionResult) main.dispatch(rhsBit.getOperand2());

			// array address expression, getValue() return exceptions.
			final ExpressionResult rl = exprResultTransformer
					.makeRepresentationReadyForConversionAndRexBoolToInt(rhsOpr1, loc, lType, node);
			final ExpressionResult rr = exprResultTransformer
					.makeRepresentationReadyForConversionAndRexBoolToInt(rhsOpr2, loc, lType, node);
			builder.addAllExceptLrValue(rl);
			builder.addAllExceptLrValue(rr);
			final Expression opr1 = rl.getLrValue().getValue();
			final Expression opr2 = rr.getLrValue().getValue();

			final Expression opr1Signed =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, opr1, lit0);
			final Expression opr2Signed =
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, opr2, lit0);
			final Expression oprSigned = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
					opr1Signed, opr2Signed);

			if (rhsBit.getOperator() == IASTBinaryExpression.op_binaryAnd) {
				final String funcname = "bitwiseAnd";
				final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + funcname;
				final Expression funcAnd = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
						new Expression[] { opr1, opr2 }, mTypeHandler.getBoogieTypeForCType(lType));

				final Expression leftOpr1 =
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT, leftVal, opr1);
				final Expression leftOpr2 =
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT, leftVal, opr2);
				final Expression andLe = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
						leftOpr1, leftOpr2);

				final Expression andElse =
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT, leftVal, funcAnd);
				final Expression resultIte =
						ExpressionFactory.constructIfThenElseExpression(loc, oprSigned, andLe, andElse);
				final CPrimitive typeOfResult = new CPrimitive(CPrimitives.INT);
				final RValue rval = new RValue(resultIte, typeOfResult, true, false);
				builder.setLrValue(rval);
				return builder.build();

				/*
				 * } else if (rhs_bit.getOperator() == IASTBinaryExpression.op_binaryOr) { return builder.build();
				 */
			}
			throw new UnsupportedOperationException(
					"No general rules for bitiwse operator other than &, | in relational");
		}
		if (node.getOperand2() instanceof IASTUnaryExpression) {
			final IASTUnaryExpression uIexpr = (IASTUnaryExpression) node.getOperand2();
			if (!isBitwiseOperator(uIexpr.getOperator())) {
				// TODO, x = expr1 + ~expr2?
				throw new UnsupportedOperationException("ToDo, x = expr1 + ~expr2?...");
			}
		}
		return builder.build();
	}

	/**
	 * Method to make assume abstraction for general bitwise and/or
	 * 
	 * @param bexpr
	 * 
	 */
	private static IfStatement assumeIte(final CHandler cHandler, final ProcedureManager procedureManager,
			final ExpressionResultBuilder builder, final CType lType, final IASTBinaryExpression node,
			final ExpressionResult leftOperand, final INameHandler nameHandler,
			final AuxVarInfoBuilder auxVarInfoBuilder, final FlatSymbolTable symbolTable,
			final ExpressionResultTransformer exprResultTransformer, final ExpressionTranslation expressionTranslation,
			final IDispatcher main, final IASTBinaryExpression rhsBit, final Expression opr1, final Expression opr2,
			final Expression rhsIte, final Expression formulaLeft, final VariableLHS idLhs) {
		// We need to create a new id expression to store the expression here.
		// leftOperand we supposed to be an idExpression, implicit cast
		final IdentifierExpression idLeft = (IdentifierExpression) leftOperand.getLrValue().getValue();
		final ILocation loc = idLhs.getLoc();
		// Create the LRValue for the assignment statement.
		final VariableLHS idLhsLeft =
				new VariableLHS(loc, idLeft.getType(), idLeft.getIdentifier(), idLeft.getDeclarationInformation());
		final LRValue idLhsLrVal = new LocalLValue(idLhsLeft, lType, false, false, null);

		final Expression lit0 = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		final ExpressionResult rhsOpr2 = (ExpressionResult) main.dispatch(rhsBit.getOperand2());

		final Expression opr1Signed =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, opr1, lit0);
		final Expression opr2Signed =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, opr2, lit0);
		final Expression oprSigned =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, opr1Signed, opr2Signed);

		// for the elseStmt, we write it to an assignment with __VERRIFIER_nondet_int()
		// (nondet funciton) call
		final String nondetName = "__VERRIFIER_nondet_int()";
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final AuxVarInfo auxvarinfo = auxVarInfoBuilder.constructAuxVarInfo(loc, lType, SFO.AUXVAR.NONDET);
		resultBuilder.addDeclaration(auxvarinfo.getVarDec());
		resultBuilder.addAuxVar(auxvarinfo);

		final LRValue returnValue = new RValue(auxvarinfo.getExp(), lType);
		resultBuilder.setLrValue(returnValue);
		expressionTranslation.addAssumeValueInRangeStatements(loc, returnValue.getValue(), returnValue.getCType(),
				resultBuilder);
		assert CTranslationUtil.isAuxVarMapComplete(nameHandler, resultBuilder.getDeclarations(),
				resultBuilder.getAuxVars());
		final ExpressionResult nondetResult = resultBuilder.build();
		final ExpressionResult nondetSwitched = exprResultTransformer
				.makeRepresentationReadyForConversionAndRexBoolToInt(nondetResult, loc, lType, node);
		final ExpressionResult assignElse =
				cHandler.makeAssignment(loc, idLhsLrVal, leftOperand.getNeighbourUnionFields(), nondetSwitched, node);

		// We need to register this auxiliary variable, and this is local variable;

		// create the CDelaration for auxVar
		final CDeclaration auxCdecl = new CDeclaration(lType, nondetName);
		final DeclarationInformation auxDeclInfo =
				new DeclarationInformation(StorageClass.LOCAL, procedureManager.getCurrentProcedureID());
		final SymbolTableValue auxStv = new SymbolTableValue(auxvarinfo.getExp().getIdentifier(),
				auxvarinfo.getVarDec(), auxCdecl, auxDeclInfo, node, false);
		symbolTable.storeCSymbol(node, auxvarinfo.getExp().getIdentifier(), auxStv);

		final ExpressionResult rightOperandSwitched =
				exprResultTransformer.makeRepresentationReadyForConversionAndRexBoolToInt(rhsOpr2, loc, lType, node);
		builder.addAllIncludingLrValue(rightOperandSwitched);

		final AssumeStatement assumePos = new AssumeStatement(loc, oprSigned);
		final AssumeStatement assumeStmt = new AssumeStatement(loc, formulaLeft);
		final AssignmentStatement assignVal = StatementFactory.constructAssignmentStatement(loc,
				new LeftHandSide[] { idLhs }, new Expression[] { rhsIte });

		final ArrayList<Statement> stmt = new ArrayList<>(assignElse.getStatements());
		final ArrayList<Declaration> decl = new ArrayList<>(assignElse.getDeclarations());
		final List<Overapprox> overappr = new ArrayList<>();

		stmt.addAll(CTranslationUtil.createHavocsForAuxVars(assignElse.getAuxVars()));
		overappr.addAll(assignElse.getOverapprs());
		final ExpressionResult exprAssign =
				new ExpressionResult(stmt, assignElse.getLrValue(), decl, Collections.emptySet(), overappr);

		final List<Statement> thenStmt = new ArrayList<>();
		final List<Statement> elseStmt = new ArrayList<>(exprAssign.getStatements());
		thenStmt.add(assignVal);
		thenStmt.add(assumePos);
		thenStmt.add(assumeStmt);
		return new IfStatement(loc, oprSigned, thenStmt.toArray(new Statement[thenStmt.size()]),
				elseStmt.toArray(new Statement[elseStmt.size()]));

	}

	/**
	 * method to decide if an expression has bitwise operator
	 * 
	 * @param bexpr
	 *            for now we consider all binary cases, because the unary complement rule is not clear yet.
	 * 
	 */
	public static boolean containBitwise(final IASTExpression expr) {
		if (!(expr instanceof IASTBinaryExpression)) {
			if (expr instanceof IASTUnaryExpression) {
				final IASTUnaryExpression uexpr = (IASTUnaryExpression) expr;
				if (uexpr.getOperator() == IASTUnaryExpression.op_tilde) {
					return true;
				}
			}
			return false;
		}
		final IASTBinaryExpression bexpr = (IASTBinaryExpression) expr;
		switch (bexpr.getOperator()) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryXorAssign:
			return true;
		default: {
			return false;
		}
		}
	}

	// Justify if an operator is bitwise operator
	public static boolean isBitwiseOperator(final int opcd) {

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
	public static boolean isCompareOperator(final Expression expr) {
		return expr instanceof IfThenElseExpression;
	}

	// Justify if an operator is bitwise operator we should return a list that
	// collect all the bit-wise expressions.
	public static IASTBinaryExpression getBitwiseBinary(final IASTBinaryExpression binExpr) {
		final int opcd = binExpr.getOperator();
		switch (opcd) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryXorAssign:
			return binExpr;
		default: {
			final boolean leftBit = containBitwise(binExpr.getOperand1());
			final boolean rightBit = containBitwise(binExpr.getOperand2());
			if (leftBit) {
				return getBitwiseBinary((IASTBinaryExpression) binExpr.getOperand1());
			}
			if (rightBit) {
				return getBitwiseBinary((IASTBinaryExpression) binExpr.getOperand2());
			}
			throw new UnsupportedOperationException(
					"Neithter opertands of the %s contatins bitwise operation!" + binExpr.toString());
		}
		}
	}

	private void declareBitvectorFunction(final ILocation loc, final String prefixedFunctionName,
			final boolean boogieResultTypeBool, final CPrimitive resultCType, final CPrimitive... paramCType) {
		final String functionName = prefixedFunctionName.substring(1);
		final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
				new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
		final Attribute[] attributes = { attribute };
		mFunctionDeclarations.declareFunction(loc, SFO.AUXILIARY_FUNCTION_PREFIX + functionName, attributes,
				boogieResultTypeBool, resultCType, paramCType);
	}

	private Expression constructShiftWithLiteralOptimization(final ILocation loc, final Expression left,
			final CPrimitive typeRight, final BigInteger integerLiteralValue, final Operator op1) {
		// 2017-11-18 Matthias: this could be done analogously in the
		// bitprecise translation
		final int exponent;
		try {
			exponent = integerLiteralValue.intValueExact();
		} catch (final ArithmeticException ae) {
			throw new UnsupportedOperationException("rhs of leftshift is larger than C standard allows " + ae);
		}
		final BigInteger shiftFactorBigInt = BigInteger.valueOf(2).pow(exponent);
		final Expression shiftFactorExpr = mTypeSizes.constructLiteralForIntegerType(loc, typeRight, shiftFactorBigInt);
		return ExpressionFactory.newBinaryExpression(loc, op1, left, shiftFactorExpr);
	}

}
