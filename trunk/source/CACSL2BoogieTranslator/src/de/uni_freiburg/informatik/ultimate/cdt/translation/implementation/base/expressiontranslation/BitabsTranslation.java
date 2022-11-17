/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2021 Cyrus Liu (yliu195@stevens.edu)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Thomas Lang
 * Copyright (C) 2015-2022 University of Freiburg
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

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Cyrus Liu (yliu195@stevens.edu)
 *
 */
public class BitabsTranslation {
	private final FunctionDeclarations mFunctionDeclarations;
	private final TypeSizes mTypeSizes;
	private final ITypeHandler mTypeHandler;

	public BitabsTranslation(final TypeSizes typeSizes, final ITypeHandler typeHandler,
			final FunctionDeclarations functionDeclarations) {
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;
		mFunctionDeclarations = functionDeclarations;
	}

	public Expression abstractAnd(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight) {
		// 0 & a = a & 0 = 0
		if (left instanceof IntegerLiteral && ((IntegerLiteral) left).getValue().equals("0")) {
			return left;
		}
		if (right instanceof IntegerLiteral && ((IntegerLiteral) right).getValue().equals("0")) {
			return right;
		}
		// a & a = a
		if (left instanceof IntegerLiteral && right instanceof IntegerLiteral
				&& ((IntegerLiteral) left).getValue().equals(((IntegerLiteral) right).getValue())) {
			return left;
		}
		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		final Expression leftEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, zero);
		final Expression rightEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, right, zero);
		final Expression oneEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftEqualsZero, rightEqualsZero);
		final Expression leftEqualsRight = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, right);

		final Expression function = declareAndApplyFunction(loc, "bitwiseAnd", typeLeft,
				new CPrimitive[] { typeLeft, typeRight }, new Expression[] { left, right });

		return ExpressionFactory.constructIfThenElseExpression(loc, oneEqualsZero, zero,
				ExpressionFactory.constructIfThenElseExpression(loc, leftEqualsRight, left, function));
	}

	public Expression abstractOr(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight) {
		// 0 | a = a | 0 = a
		if (left instanceof IntegerLiteral && ((IntegerLiteral) left).getValue().equals("0")) {
			return right;
		}
		if (right instanceof IntegerLiteral && ((IntegerLiteral) right).getValue().equals("0")) {
			return left;
		}
		// a | a = a
		if (left instanceof IntegerLiteral && right instanceof IntegerLiteral
				&& ((IntegerLiteral) left).getValue().equals(((IntegerLiteral) right).getValue())) {
			return left;
		}

		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		final Expression leftEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, zero);
		final Expression rightEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, right, zero);
		final Expression leftEqualsRight = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, right);
		final Expression leftEqualsZeroOrRight =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftEqualsZero, leftEqualsRight);

		final Expression function = declareAndApplyFunction(loc, "bitwiseOr", typeLeft,
				new CPrimitive[] { typeLeft, typeRight }, new Expression[] { left, right });

		return ExpressionFactory.constructIfThenElseExpression(loc, leftEqualsZeroOrRight, right,
				ExpressionFactory.constructIfThenElseExpression(loc, rightEqualsZero, left, function));
	}

	// TODO: Previously there was another optimization here, but this seemed unsound in general.
	// So I removed it for now, until we have a fix.
	public Expression abstractShiftLeft(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		final BigInteger shiftLeftLiteralValue = mTypeSizes.extractIntegerValue(right, typeRight, hook);
		if (shiftLeftLiteralValue != null) {
			return constructShiftWithLiteralOptimization(loc, left, typeRight, shiftLeftLiteralValue,
					Operator.ARITHMUL);
		}
		return declareAndApplyFunction(loc, "shiftLeft", typeLeft, new CPrimitive[] { typeLeft, typeRight },
				new Expression[] { left, right });
	}

	public Expression abstractShiftRight(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final IASTNode hook) {
		final BigInteger shiftRightLiteralValue = mTypeSizes.extractIntegerValue(right, typeRight, hook);
		if (shiftRightLiteralValue != null) {
			return constructShiftWithLiteralOptimization(loc, left, typeRight, shiftRightLiteralValue,
					Operator.ARITHDIV);
		}
		return declareAndApplyFunction(loc, "shiftRight", typeLeft, new CPrimitive[] { typeLeft, typeRight },
				new Expression[] { left, right });
	}

	public Expression abstractXor(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight) {
		// 0 ^ a = a ^ 0 = 0
		if (left instanceof IntegerLiteral && ((IntegerLiteral) left).getValue().equals("0")) {
			return right;
		}
		if (right instanceof IntegerLiteral && ((IntegerLiteral) right).getValue().equals("0")) {
			return left;
		}
		// a ^ a = 0
		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		if (left instanceof IntegerLiteral && right instanceof IntegerLiteral
				&& ((IntegerLiteral) left).getValue().equals(((IntegerLiteral) right).getValue())) {
			return zero;
		}

		final Expression leftEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, zero);
		final Expression rightEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, right, zero);
		final Expression leftEqualsRight = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, right);

		final Expression function = declareAndApplyFunction(loc, "bitwiseXor", typeLeft,
				new CPrimitive[] { typeLeft, typeRight }, new Expression[] { left, right });

		return ExpressionFactory.constructIfThenElseExpression(loc, leftEqualsZero, right,
				ExpressionFactory.constructIfThenElseExpression(loc, rightEqualsZero, left,
						ExpressionFactory.constructIfThenElseExpression(loc, leftEqualsRight, zero, function)));
	}

	/*
	 * solution: integer eqauls to 0 or 1, complement-logic rule
	 */
	public Expression abstractCompl(final ILocation loc, final Expression expr, final CPrimitive type) {
		return declareAndApplyFunction(loc, "bitwiseComplement", type, new CPrimitive[] { type },
				new Expression[] { expr });
	}

	// TODO: This is more of a workaround, ideally we should handle everything on statements.
	// But to be more precise, this requires additional aux-variables.
	// TODO: We could use more precise assumptions, if the expression has a signed type
	public Result abstractAssign(final ExpressionResultTransformer exprResultTransformer, final IDispatcher main,
			final LocationFactory locationFactory, final IASTBinaryExpression node,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
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

		// Create the LRValue for the assignment statement.
		final VariableLHS idLhsLeft =
				new VariableLHS(loc, idLeft.getType(), idLeft.getIdentifier(), idLeft.getDeclarationInformation());

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final CPrimitive lType = (CPrimitive) leftOperand.getLrValue().getCType().getUnderlyingType();

		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		final AuxVarInfo auxvarinfo = auxVarInfoBuilder.constructAuxVarInfo(loc, lType, SFO.AUXVAR.NONDET);
		builder.addDeclaration(auxvarinfo.getVarDec());
		builder.addAuxVar(auxvarinfo);
		final IdentifierExpression auxvar = auxvarinfo.getExp();

		// for declare the auxiliary vars.
		if (node.getOperand2() instanceof IASTBinaryExpression) {
			// for the general bitwise assignment case, we build up assume statements.
			final IASTBinaryExpression binary = (IASTBinaryExpression) node.getOperand2();
			final ExpressionResult rhsOpr1 = (ExpressionResult) main.dispatch(binary.getOperand1());
			final ExpressionResult rhsOpr2 = (ExpressionResult) main.dispatch(binary.getOperand2());

			// array address expression, getValue() return exceptions.
			final ExpressionResult rl = exprResultTransformer
					.makeRepresentationReadyForConversionAndRexBoolToInt(rhsOpr1, loc, lType, node);
			final ExpressionResult rr = exprResultTransformer
					.makeRepresentationReadyForConversionAndRexBoolToInt(rhsOpr2, loc, lType, node);
			builder.addAllExceptLrValue(rl);
			builder.addAllExceptLrValue(rr);
			final Expression left = rl.getLrValue().getValue();
			final Expression right = rr.getLrValue().getValue();

			final Expression leftEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, zero);
			final Expression rightEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, right, zero);
			final Expression leftEqualsRight = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, right);

			final Expression leftNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, left, zero);
			final Expression rightNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, right, zero);

			final Expression oneNegative =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftNegative, rightNegative);
			final Expression bothNonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, left, zero),
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, right, zero));
			final Expression bothNegative =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftNegative, rightNegative);

			final Expression sum = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHPLUS, left, right);

			if (binary.getOperator() == IASTBinaryExpression.op_binaryAnd) {
				final Expression oneEqualsZero =
						ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftEqualsZero, rightEqualsZero);
				final Expression function = declareAndApplyFunction(loc, "bitwiseAnd", lType,
						new CPrimitive[] { lType, lType }, new Expression[] { left, right });

				final Expression lessThanEqualBoth = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, left),
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, right));

				// If a >= 0 and b >= 0, then a & b <= a and a & b <= b
				final Expression maximum =
						ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative, lessThanEqualBoth);
				// If a >= b or b >= 0, then a & b >= 0
				final Expression nonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
						bothNegative, ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar, zero));
				// If a < 0 or b < 0, then a & b > a + b
				final Expression greaterSum = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
						bothNonNegative, ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, auxvar, sum));

				// 0 & a = a & 0 = 0
				// a & a = a
				final Statement ifInner =
						StatementFactory.constructIfStatement(loc, leftEqualsRight,
								new Statement[] { StatementFactory.constructAssignmentStatement(loc, idLhsLeft, left) },
								new Statement[] {
										StatementFactory.constructAssignmentStatement(loc, auxvarinfo.getLhs(),
												function),
										new AssumeStatement(loc, maximum), new AssumeStatement(loc, nonNegative),
										new AssumeStatement(loc, greaterSum),
										StatementFactory.constructAssignmentStatement(loc, idLhsLeft, auxvar) });
				final Statement ifOuter = StatementFactory.constructIfStatement(loc, oneEqualsZero,
						new Statement[] { StatementFactory.constructAssignmentStatement(loc, idLhsLeft, zero) },
						new Statement[] { ifInner });

				builder.addStatement(ifOuter);
				return builder.build();

			}
			if (binary.getOperator() == IASTBinaryExpression.op_binaryOr) {
				final Expression leftEqualsZeroOrRight =
						ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftEqualsZero, leftEqualsRight);
				final Expression function = declareAndApplyFunction(loc, "bitwiseOr", lType,
						new CPrimitive[] { lType, lType }, new Expression[] { left, right });

				// If a >= 0 and b >= 0, then a | b >= a and a | b >= b
				final Expression greaterEqualBoth = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar, left),
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar, right));
				final Expression minimum =
						ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative, greaterEqualBoth);
				// Otherwise a | b < 0
				final Expression negative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
						bothNonNegative, ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, auxvar, zero));
				// If a >= 0 or b >= 0, then a | b <= a + b
				final Expression leqSum = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative,
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, sum));

				// 0 | a = a | 0 = a
				// a | a = a
				final Statement ifInner =
						StatementFactory.constructIfStatement(loc, rightEqualsZero,
								new Statement[] { StatementFactory.constructAssignmentStatement(loc, idLhsLeft, left) },
								new Statement[] {
										StatementFactory.constructAssignmentStatement(loc, auxvarinfo.getLhs(),
												function),
										new AssumeStatement(loc, minimum), new AssumeStatement(loc, negative),
										new AssumeStatement(loc, leqSum),
										StatementFactory.constructAssignmentStatement(loc, idLhsLeft, auxvar) });
				final Statement ifOuter = StatementFactory.constructIfStatement(loc, leftEqualsZeroOrRight,
						new Statement[] { StatementFactory.constructAssignmentStatement(loc, idLhsLeft, right) },
						new Statement[] { ifInner });

				builder.addStatement(ifOuter);
				return builder.build();
			}
			if (binary.getOperator() == IASTBinaryExpression.op_binaryXor) {
				final Expression function = declareAndApplyFunction(loc, "bitwiseXor", lType,
						new CPrimitive[] { lType, lType }, new Expression[] { left, right });

				final Expression positive = ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, auxvar, zero);
				final Expression onePositive = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, left, zero),
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, right, zero));

				// If a and b have the same sign (i.e. both are positive or both are negative), then a ^ b > 0
				final Expression positiveCase1 =
						ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative, positive);
				final Expression positiveCase2 =
						ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, onePositive, positive);
				// If a >= 0 or b >= 0, then a ^ b <= a + b
				final Expression leqSum = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative,
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, sum));

				// 0 ^ a = a ^ 0 = a
				// a ^ a = 0
				final Statement ifInner =
						StatementFactory.constructIfStatement(loc, leftEqualsRight,
								new Statement[] { StatementFactory.constructAssignmentStatement(loc, idLhsLeft, zero) },
								new Statement[] {
										StatementFactory.constructAssignmentStatement(loc, auxvarinfo.getLhs(),
												function),
										new AssumeStatement(loc, positiveCase1),
										new AssumeStatement(loc, positiveCase2), new AssumeStatement(loc, leqSum),
										StatementFactory.constructAssignmentStatement(loc, idLhsLeft, auxvar) });
				final Statement ifMiddle = StatementFactory.constructIfStatement(loc, rightEqualsZero,
						new Statement[] { StatementFactory.constructAssignmentStatement(loc, idLhsLeft, left) },
						new Statement[] { ifInner });
				final Statement ifOuter = StatementFactory.constructIfStatement(loc, leftEqualsZero,
						new Statement[] { StatementFactory.constructAssignmentStatement(loc, idLhsLeft, right) },
						new Statement[] { ifMiddle });

				builder.addStatement(ifOuter);
				return builder.build();
			}
		}
		if (node.getOperand2() instanceof IASTUnaryExpression) {
			final IASTUnaryExpression uIexpr = (IASTUnaryExpression) node.getOperand2();
			final ExpressionResult res = exprResultTransformer.makeRepresentationReadyForConversionAndRexBoolToInt(
					(ExpressionResult) main.dispatch(uIexpr.getOperand()), loc, lType, node);
			builder.addAllExceptLrValue(res);
			final Expression expr = res.getLrValue().getValue();
			final Expression function = declareAndApplyFunction(loc, "bitwiseComplement", lType,
					new CPrimitive[] { lType }, new Expression[] { expr });
			builder.addStatement(StatementFactory.constructAssignmentStatement(loc, auxvarinfo.getLhs(), function));
			// ~a != a
			builder.addStatement(new AssumeStatement(loc,
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPNEQ, auxvar, expr)));
			// If a < 0, then ~a > 0
			builder.addStatement(new AssumeStatement(loc,
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
							ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, expr, zero),
							ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, auxvar, zero))));
			builder.addStatement(StatementFactory.constructAssignmentStatement(loc, idLhsLeft, auxvar));
			return builder.build();

		}
		throw new UnsupportedOperationException("Only the bitwise operators &, |, ^, ~ are supported.");
	}

	private Expression declareAndApplyFunction(final ILocation loc, final String functionName,
			final CPrimitive resultType, final CPrimitive[] paramTypes, final Expression[] expressions) {
		final String prefixedFunctionName = SFO.AUXILIARY_FUNCTION_PREFIX + functionName;
		final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
				new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
		mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, new Attribute[] { attribute }, false,
				resultType, paramTypes);
		return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName, expressions,
				mTypeHandler.getBoogieTypeForCType(resultType));
	}

	private Expression constructShiftWithLiteralOptimization(final ILocation loc, final Expression left,
			final CPrimitive typeRight, final BigInteger integerLiteralValue, final Operator op1) {
		// 2017-11-18 Matthias: this could be done analogously in the
		// bitprecise translation
		final int exponent;
		try {
			exponent = integerLiteralValue.intValueExact();
		} catch (final ArithmeticException ae) {
			throw new UnsupportedOperationException("RHS of shift is larger than C standard allows " + ae);
		}
		final BigInteger shiftFactorBigInt = BigInteger.valueOf(2).pow(exponent);
		final Expression shiftFactorExpr = mTypeSizes.constructLiteralForIntegerType(loc, typeRight, shiftFactorBigInt);
		return ExpressionFactory.newBinaryExpression(loc, op1, left, shiftFactorExpr);
	}
}
