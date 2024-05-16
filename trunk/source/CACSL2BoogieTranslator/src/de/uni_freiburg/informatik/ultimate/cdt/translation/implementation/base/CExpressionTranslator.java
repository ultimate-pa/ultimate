/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015-2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StaticObjectsHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.StringLiteralResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerCheckMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class is used to translate C expressions (actually ExpressionStatements) to Boogie.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CExpressionTranslator {

	private final TranslationSettings mSettings;

	private final MemoryHandler mMemoryHandler;
	private final StaticObjectsHandler mStaticObjectsHandler;

	private final ExpressionTranslation mExpressionTranslation;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final TypeSizes mTypeSizes;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	public CExpressionTranslator(final TranslationSettings settings, final MemoryHandler memoryHandler,
			final ExpressionTranslation expressionTranslation, final ExpressionResultTransformer exprResultTransformer,
			final AuxVarInfoBuilder auxVarInfoBuilder, final TypeSizes typeSizes,
			final StaticObjectsHandler staticObjectsHandler) {
		mSettings = settings;
		mMemoryHandler = memoryHandler;
		mStaticObjectsHandler = staticObjectsHandler;
		mExpressionTranslation = expressionTranslation;
		mExprResultTransformer = exprResultTransformer;
		mTypeSizes = typeSizes;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
	}

	/**
	 * Handle relational operators according to Section 6.5.8 of C11. Assumes that left (resp. right) are the results
	 * from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed).
	 */
	public ExpressionResult handleRelationalOperators(final ILocation loc, final int op, ExpressionResult left,
			ExpressionResult right) {
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";
		left = mExprResultTransformer.rexBoolToInt(left, loc);
		right = mExprResultTransformer.rexBoolToInt(right, loc);
		CType lType = left.getLrValue().getCType().getUnderlyingType();
		CType rType = right.getLrValue().getCType().getUnderlyingType();

		final Expression expr;

		// Convert integer with a value of 0 to a Null pointer if necessary
		if (lType instanceof CPrimitive && rType instanceof CPointer
				&& isNullPointerEquivalent((RValue) left.getLrValue())) {
			// FIXME: the following is a workaround for the null pointer
			left = mExprResultTransformer.performImplicitConversion(left,
					new CPointer(new CPrimitive(CPrimitives.VOID)), loc);
			lType = left.getLrValue().getCType().getUnderlyingType();
		} else if (lType instanceof CPointer && rType instanceof CPrimitive
				&& isNullPointerEquivalent((RValue) right.getLrValue())) {
			// FIXME: the following is a workaround for the null pointer
			right = mExprResultTransformer.performImplicitConversion(right,
					new CPointer(new CPrimitive(CPrimitives.VOID)), loc);
			rType = right.getLrValue().getCType().getUnderlyingType();
		}
		ExpressionResultBuilder result = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
		if (lType instanceof CPrimitive && rType instanceof CPrimitive) {
			assert lType.isRealType() && rType.isRealType() : "no real type";
			final Pair<ExpressionResult, ExpressionResult> newOps =
					mExprResultTransformer.usualArithmeticConversions(loc, left, right);
			left = newOps.getFirst();
			right = newOps.getSecond();
			result = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
			expr = mExpressionTranslation.constructBinaryComparisonExpression(loc, op, left.getLrValue().getValue(),
					(CPrimitive) left.getLrValue().getCType().getUnderlyingType(), right.getLrValue().getValue(),
					(CPrimitive) right.getLrValue().getCType().getUnderlyingType());
		} else if (lType instanceof CPointer && rType instanceof CPointer) {
			final Expression baseEquality = constructPointerComponentRelation(loc, IASTBinaryExpression.op_equals,
					left.getLrValue().getValue(), right.getLrValue().getValue(), SFO.POINTER_BASE);
			final Expression offsetRelation = constructPointerComponentRelation(loc, op, left.getLrValue().getValue(),
					right.getLrValue().getValue(), SFO.POINTER_OFFSET);
			switch (mSettings.getPointerSubtractionAndComparisonValidityCheckMode()) {
			case ASSERTandASSUME:
				final Statement assertStm = new AssertStatement(loc, baseEquality);
				final Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
				chk.annotate(assertStm);
				result.addStatement(assertStm);
				expr = offsetRelation;
				break;
			case ASSUME:
				final Statement assumeStm = new AssumeStatement(loc, baseEquality);
				result.addStatement(assumeStm);
				expr = offsetRelation;
				break;
			case IGNORE:
				// use conjunction
				expr = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, baseEquality, offsetRelation);
				// TODO: Do not use conjunction. Use nondeterministic value
				// if baseEquality does not hold.
				break;
			default:
				throw new AssertionError("unknown value");
			}

		} else {
			throw new UnsupportedOperationException("unsupported " + lType + ", " + rType);
		}
		// The result has type int (C11 6.5.8.6)
		final CPrimitive typeOfResult = new CPrimitive(CPrimitives.INT);
		final RValue rval = new RValue(expr, typeOfResult, true, false);
		return result.setLrValue(rval).build();
	}

	/**
	 * Handle additive operators according to Sections 6.5.6 of C11. Assumes that left (resp. right) are the results
	 * from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 *
	 */
	public ExpressionResult handleAdditiveOperation(final ILocation loc, final int op, ExpressionResult left,
			ExpressionResult right) {
		if (!List.of(IASTBinaryExpression.op_plus, IASTBinaryExpression.op_minus, IASTBinaryExpression.op_plusAssign,
				IASTBinaryExpression.op_minusAssign).contains(op)) {
			throw new AssertionError("no additive operation " + op);
		}
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";

		CType lType = left.getLrValue().getCType().getUnderlyingType();
		final CType rType = right.getLrValue().getCType().getUnderlyingType();

		if (lType instanceof CArray && rType.isArithmeticType()) {
			// arrays decay to pointers in this case
			assert !(((CArray) lType).getBound().getCType() instanceof CArray) : "TODO: think about this case";
			final CType valueType = ((CArray) lType).getValueType().getUnderlyingType();
			left = mExprResultTransformer.performImplicitConversion(left, new CPointer(valueType), loc);
			lType = left.getLrValue().getCType().getUnderlyingType();
		}

		final ExpressionResultBuilder builder;
		final Expression expr;
		final CType typeOfResult;
		if (lType.isArithmeticType() && rType.isArithmeticType()) {
			final Pair<ExpressionResult, ExpressionResult> newOps =
					mExprResultTransformer.usualArithmeticConversions(loc, left, right);
			left = newOps.getFirst();
			right = newOps.getSecond();
			builder = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
			typeOfResult = left.getLrValue().getCType();
			assert typeOfResult.equals(right.getLrValue().getCType());
			final CPrimitive primitiveTypeOfResult = (CPrimitive) typeOfResult.getUnderlyingType();

			addIntegerBoundsCheck(loc, builder, primitiveTypeOfResult, op, left.getLrValue().getValue(),
					right.getLrValue().getValue());
			expr = mExpressionTranslation.constructArithmeticExpression(loc, op, left.getLrValue().getValue(),
					primitiveTypeOfResult, right.getLrValue().getValue(), primitiveTypeOfResult);
		} else if (lType instanceof CPointer && rType.isArithmeticType()) {
			typeOfResult = left.getLrValue().getCType();
			final CType pointsToType = ((CPointer) typeOfResult).getPointsToType();
			final ExpressionResult re = mMemoryHandler.doPointerArithmeticWithConversion(op, loc,
					left.getLrValue().getValue(), (RValue) right.getLrValue(), pointsToType);
			builder = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
			builder.addAllExceptLrValue(re);
			expr = re.getLrValue().getValue();
			addOffsetInBoundsCheck(loc, expr, builder);
		} else if (lType.isArithmeticType() && rType instanceof CPointer) {
			if (op != IASTBinaryExpression.op_plus && op != IASTBinaryExpression.op_plusAssign) {
				throw new AssertionError("lType arithmetic, rType CPointer only legal if op is plus");
			}
			typeOfResult = right.getLrValue().getCType();
			final CType pointsToType = ((CPointer) typeOfResult).getPointsToType();
			final ExpressionResult re = mMemoryHandler.doPointerArithmeticWithConversion(op, loc,
					right.getLrValue().getValue(), (RValue) left.getLrValue(), pointsToType);
			builder = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
			builder.addAllExceptLrValue(re);
			expr = re.getLrValue().getValue();
			addOffsetInBoundsCheck(loc, expr, builder);
		} else if (lType instanceof CPointer && rType instanceof CPointer) {
			if (op != IASTBinaryExpression.op_minus && op != IASTBinaryExpression.op_minusAssign) {
				throw new AssertionError("lType arithmetic, rType CPointer only legal if op is minus");
			}
			// C11 6.5.6.9 says
			// "The size of the result is implementation-defined,
			// and its type (a signed integer type) is ptrdiff_t defined in
			// the <stddef.h> header."
			// We randomly choose the type whose Boogie translation we use to
			// represent pointer components.
			typeOfResult = mExpressionTranslation.getCTypeOfPointerComponents();
			CType pointsToType;
			{
				final CType leftPointsToType = ((CPointer) lType).getPointsToType();
				final CType rightPointsToType = ((CPointer) rType).getPointsToType();
				if (!leftPointsToType.isCompatibleWith(rightPointsToType)) {
					throw new UnsupportedOperationException(
							"incompatible pointers: pointsto " + leftPointsToType + " " + rightPointsToType);
				}
				pointsToType = leftPointsToType;
			}
			builder = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
			addBaseEqualityCheck(loc, left.getLrValue().getValue(), right.getLrValue().getValue(), builder);
			expr = doPointerSubtraction(loc, left.getLrValue().getValue(), right.getLrValue().getValue(), pointsToType);

		} else {
			throw new UnsupportedOperationException("non-standard case of pointer arithmetic");
		}
		final RValue rval = new RValue(expr, typeOfResult, false, false);
		builder.setLrValue(rval);

		if (left instanceof StringLiteralResult) {
			/*
			 * if we had a StringLiteralResult as input, we have to restore the StringLiteralResult from the
			 * ExpressionResult.
			 */
			builder.getDeclarations().forEach(decl -> mStaticObjectsHandler
					.addGlobalVarDeclarationWithoutCDeclaration((VariableDeclaration) decl));
			mStaticObjectsHandler.addStatementsForUltimateInit(builder.getStatements());
			return new StringLiteralResult(builder.getLrValue(), builder.getOverappr(),
					((StringLiteralResult) left).getAuxVar(), ((StringLiteralResult) left).getLiteralString(),
					((StringLiteralResult) left).overApproximatesLongStringLiteral());

		}
		return builder.build();
	}

	/**
	 * Handle unary arithmetic operators according to Section 6.5.3.3 of C11. Assumes that left (resp. right) are the
	 * results from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed).
	 */
	public ExpressionResult handleUnaryArithmeticOperators(final ILocation loc, final int op,
			ExpressionResult operand) {
		assert operand.getLrValue() instanceof RValue : "no RValue";
		final CType inputType = operand.getLrValue().getCType().getUnderlyingType();

		switch (op) {
		case IASTUnaryExpression.op_not: {
			if (!inputType.isScalarType()) {
				throw new IllegalArgumentException("scalar type required");
			}
			final Expression negated;
			if (operand.getLrValue().isBoogieBool()) {
				// in Boogie already represented by bool, we only negate
				negated = ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG,
						operand.getLrValue().getValue());
			} else {
				final Expression rhsOfComparison;
				if (inputType instanceof CPointer) {
					rhsOfComparison = mExpressionTranslation.constructNullPointer(loc);
				} else if (inputType instanceof CEnum) {
					final CPrimitive intType = new CPrimitive(CPrimitives.INT);
					rhsOfComparison = mExpressionTranslation.constructZero(loc, intType);
				} else if (inputType instanceof CPrimitive) {
					rhsOfComparison = mExpressionTranslation.constructZero(loc, inputType);
				} else {
					throw new AssertionError("illegal case");
				}
				negated = mExpressionTranslation.constructBinaryEqualityExpression(loc, IASTBinaryExpression.op_equals,
						operand.getLrValue().getValue(), inputType, rhsOfComparison, inputType);

			}
			final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllExceptLrValue(operand);
			// C11 6.5.3.3.5 The result has type int.
			final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
			// type of Operator.COMPEQ expression is bool
			final boolean isBoogieBool = true;
			final RValue rval = new RValue(negated, resultType, isBoogieBool);
			return builder.setLrValue(rval).build();
		}
		case IASTUnaryExpression.op_plus: {
			if (!inputType.isArithmeticType()) {
				throw new UnsupportedOperationException("arithmetic type required");
			}
			if (inputType.isArithmeticType()) {
				operand = mExprResultTransformer.rexBoolToInt(operand, loc);
				operand = mExprResultTransformer.promoteToIntegerIfNecessary(loc, operand);
			}
			return operand;
		}
		case IASTUnaryExpression.op_minus:
		case IASTUnaryExpression.op_tilde:
			if (!inputType.isArithmeticType()) {
				throw new UnsupportedOperationException("arithmetic type required");
			}
			operand = mExprResultTransformer.rexBoolToInt(operand, loc);
			operand = mExprResultTransformer.promoteToIntegerIfNecessary(loc, operand);
			final CPrimitive resultType = (CPrimitive) operand.getLrValue().getCType();
			final ExpressionResultBuilder result = new ExpressionResultBuilder().addAllExceptLrValue(operand);
			if (op == IASTUnaryExpression.op_minus && resultType.isIntegerType()) {
				addIntegerBoundsCheck(loc, result, resultType, op, operand.getLrValue().getValue());
			}
			final Expression bwexpr = mExpressionTranslation.constructUnaryExpression(loc, op,
					operand.getLrValue().getValue(), resultType);
			final RValue rval = new RValue(bwexpr, resultType, false);
			return result.setLrValue(rval).build();
		default:
			throw new IllegalArgumentException("not a unary arithmetic operator " + op);
		}
	}

	/**
	 * Handle equality operators according to Section 6.5.7 of C11. Assumes that left (resp. right) are the results from
	 * handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 *
	 */
	public ExpressionResult handleBitshiftOperation(final ILocation loc, final int op, final ExpressionResult left,
			final ExpressionResult right) {
		if (!List
				.of(IASTBinaryExpression.op_shiftLeft, IASTBinaryExpression.op_shiftRight,
						IASTBinaryExpression.op_shiftLeftAssign, IASTBinaryExpression.op_shiftRightAssign)
				.contains(op)) {
			throw new AssertionError("no bitshift " + op);
		}
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";
		final CType lType = left.getLrValue().getCType().getUnderlyingType();
		final CType rType = right.getLrValue().getCType().getUnderlyingType();
		if (!rType.isIntegerType() || !lType.isIntegerType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		final ExpressionResult leftPromoted = mExprResultTransformer.promoteToIntegerIfNecessary(loc, left);
		final CPrimitive typeOfResult = (CPrimitive) leftPromoted.getLrValue().getCType().getUnderlyingType();
		final ExpressionResult rightConverted =
				mExprResultTransformer.performImplicitConversion(right, typeOfResult, loc);

		final ExpressionResult result =
				mExpressionTranslation.handleBitshiftExpression(loc, op, leftPromoted.getLrValue().getValue(),
						typeOfResult, rightConverted.getLrValue().getValue(), typeOfResult, mAuxVarInfoBuilder);
		final ExpressionResultBuilder builder =
				new ExpressionResultBuilder().addAllExceptLrValue(leftPromoted, rightConverted);
		return builder.addAllIncludingLrValue(result).build();
	}

	/**
	 * Handle multiplicative operators according to Sections 6.5.5 of C11. Assumes that left (resp. right) are the
	 * results from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 *
	 */
	public ExpressionResult handleMultiplicativeOperation(final ILocation loc, final int op, ExpressionResult left,
			ExpressionResult right) {
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";
		final CType lType = left.getLrValue().getCType().getUnderlyingType();
		final CType rType = right.getLrValue().getCType().getUnderlyingType();
		if (!rType.isArithmeticType() || !lType.isArithmeticType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		if (op == IASTBinaryExpression.op_divide || op == IASTBinaryExpression.op_modulo) {
			right = addDivisionByZeroCheck(loc, right);
		}
		final Pair<ExpressionResult, ExpressionResult> newOps =
				mExprResultTransformer.usualArithmeticConversions(loc, left, right);
		left = newOps.getFirst();
		right = newOps.getSecond();
		final CPrimitive typeOfResult = (CPrimitive) left.getLrValue().getCType().getUnderlyingType();
		assert typeOfResult.equals(right.getLrValue().getCType().getUnderlyingType());

		final ExpressionResultBuilder result = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
		switch (op) {
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign:
			addIntegerBoundsCheck(loc, result, typeOfResult, op, left.getLrValue().getValue(),
					right.getLrValue().getValue());
			break;
		case IASTBinaryExpression.op_modulo:
		case IASTBinaryExpression.op_moduloAssign:
			// no integer bounds check needed
			break;
		default:
			throw new AssertionError("no multiplicative " + op);
		}

		final Expression expr = mExpressionTranslation.constructArithmeticExpression(loc, op,
				left.getLrValue().getValue(), typeOfResult, right.getLrValue().getValue(), typeOfResult);
		final RValue rval = new RValue(expr, typeOfResult, false, false);
		return result.setLrValue(rval).build();
	}

	/**
	 * Handle equality operators according to Section 6.5.9 of C11. Assumes that left (resp. right) are the results from
	 * handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 */
	public ExpressionResult handleEqualityOperators(final ILocation loc, final int op, ExpressionResult left,
			ExpressionResult right) {
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";
		{
			final CType lType = left.getLrValue().getCType().getUnderlyingType();
			final CType rType = right.getLrValue().getCType().getUnderlyingType();
			// FIXME Matthias 2015-09-05: operation only legal if both have type
			// CPointer I guess the following implicit casts are a workaround
			// for arrays (or structs or union?)
			if (lType instanceof CPointer || rType instanceof CPointer) {
				if (!(lType instanceof CPointer)) {
					// FIXME: the following is a workaround for the null pointer
					left = mExprResultTransformer.performImplicitConversion(left,
							new CPointer(new CPrimitive(CPrimitives.VOID)), loc);
				}
				if (!(rType instanceof CPointer)) {
					// FIXME: the following is a workaround for the null pointer
					right = mExprResultTransformer.performImplicitConversion(right,
							new CPointer(new CPrimitive(CPrimitives.VOID)), loc);
				}
			} else if (lType.isArithmeticType() && rType.isArithmeticType()) {
				final Pair<ExpressionResult, ExpressionResult> newOps =
						mExprResultTransformer.usualArithmeticConversions(loc, left, right);
				left = newOps.getFirst();
				right = newOps.getSecond();
			} else {
				throw new UnsupportedOperationException("unsupported " + rType + ", " + lType);
			}
		}
		// The result has type int (C11 6.5.9.1)
		final CPrimitive typeOfResult = new CPrimitive(CPrimitives.INT);
		final Expression expr =
				mExpressionTranslation.constructBinaryEqualityExpression(loc, op, left.getLrValue().getValue(),
						left.getLrValue().getCType(), right.getLrValue().getValue(), right.getLrValue().getCType());
		final RValue rval = new RValue(expr, typeOfResult, true, false);
		return new ExpressionResultBuilder().addAllExceptLrValue(left, right).setLrValue(rval).build();
	}

	/**
	 * Handle bitwise AND, bitwise XOR, and bitwise OR operators according to sections 6.5.10, 6.5.11, 6.5.12 of C11.
	 * Assumes that left (resp. right) are the results from handling the operands. Requires that the {@link LRValue} of
	 * operands is an {@link RValue} (i.e., switchToRValueIfNecessary was applied if needed). requires that the Boogie
	 * expressions in left (resp. right) are a non-boolean representation of these results (i.e.,
	 * rexBoolToIntIfNecessary() has already been applied if needed).
	 *
	 */
	public ExpressionResult handleBitwiseArithmeticOperation(final ILocation loc, final int op, ExpressionResult left,
			ExpressionResult right) {
		if (!List.of(IASTBinaryExpression.op_binaryAnd, IASTBinaryExpression.op_binaryXor,
				IASTBinaryExpression.op_binaryOr, IASTBinaryExpression.op_binaryAndAssign,
				IASTBinaryExpression.op_binaryXorAssign, IASTBinaryExpression.op_binaryOrAssign).contains(op)) {
			throw new AssertionError("no bitwise arithmetic operation " + op);
		}
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";
		final CType lType = left.getLrValue().getCType().getUnderlyingType();
		final CType rType = right.getLrValue().getCType().getUnderlyingType();
		if (!rType.isIntegerType() || !lType.isIntegerType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		final Pair<ExpressionResult, ExpressionResult> newOps =
				mExprResultTransformer.usualArithmeticConversions(loc, left, right);
		left = newOps.getFirst();
		right = newOps.getSecond();
		final CPrimitive typeOfResult = (CPrimitive) left.getLrValue().getCType().getUnderlyingType();
		assert typeOfResult.equals(left.getLrValue().getCType().getUnderlyingType());
		final ExpressionResult result =
				mExpressionTranslation.handleBinaryBitwiseExpression(loc, op, left.getLrValue().getValue(),
						typeOfResult, right.getLrValue().getValue(), typeOfResult, mAuxVarInfoBuilder);
		return new ExpressionResultBuilder().addAllExceptLrValue(left, right).addAllIncludingLrValue(result).build();
	}

	/**
	 * Handle postfix increment and decrement operators according to Section 6.5.2.4 of C11. We translate the expression
	 * <code>LV++</code> to an auxiliary variable <code>t~post</code> and add to the resulting {@link ExpressionResult}
	 * the two assignments <code>t~post := LV</code> and <code>LV := t~post + 1</code>. Hence the auxiliary variable
	 * <code>t~post</code> stores the old value of the object to which the lvalue <code>LV</code> refers.
	 *
	 * @param funMakeAssignment
	 *            A function that takes an {@link ExpressionResult} containing <code>t~post + 1</code> and produces an
	 *            {@link ExpressionResult} containing <code>LV := t~post + 1</code>. Usually, this is an invocation of
	 *            {@link CHandler#makeAssignment(ILocation, LRValue, java.util.Collection, ExpressionResult, IASTNode)}.
	 */
	public Result handlePostfixIncrementAndDecrement(final ILocation loc, final int postfixOp, ExpressionResult exprRes,
			final IASTNode hook, final Function<ExpressionResult, ExpressionResult> funMakeAssignment) {
		assert !exprRes.getLrValue().isBoogieBool();
		exprRes = mExprResultTransformer.switchToRValue(exprRes, loc, hook);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllIncludingLrValue(exprRes);

		// In this case we need a temporary variable for the old value
		final AuxVarInfo auxvar =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, exprRes.getLrValue().getCType(), SFO.AUXVAR.POST_MOD);
		builder.addAuxVarWithDeclaration(auxvar);

		// assign the old value to the temporary variable
		final LeftHandSide[] tmpAsLhs = new LeftHandSide[] { auxvar.getLhs() };
		final Expression[] oldValue = new Expression[] { exprRes.getLrValue().getValue() };
		builder.addStatement(StatementFactory.constructAssignmentStatement(loc, tmpAsLhs, oldValue));
		final CType oType = exprRes.getLrValue().getCType().getUnderlyingType();
		final RValue tmpRValue = new RValue(auxvar.getExp(), oType);

		final int op;
		if (postfixOp == IASTUnaryExpression.op_postFixIncr) {
			op = IASTBinaryExpression.op_plus;
		} else if (postfixOp == IASTUnaryExpression.op_postFixDecr) {
			op = IASTBinaryExpression.op_minus;
		} else {
			throw new AssertionError("no postfix");
		}

		// in-/decremented value
		final Expression valueXcremented = constructXcrementedValue(loc, builder, oType, op, tmpRValue.getValue());

		builder.setOrResetLrValue(new RValue(valueXcremented, oType, false, false));
		final ExpressionResult assign = funMakeAssignment.apply(builder.build());

		return new ExpressionResultBuilder().addAllExceptLrValue(assign).setLrValue(tmpRValue).build();
	}

	/**
	 * Handle prefix increment and decrement operators according to Section 6.5.3.1 of C11. We translate the expression
	 * <code>++LV</code> to an auxiliary variable <code>t~pre</code> and add to the resulting {@link ExpressionResult}
	 * the two assignments <code>t~pre := LV+1</code> and <code>LV := t~pre</code>. Hence, the auxiliary variable
	 * <code>t~pre</code> stores the new value of the object to which the lvalue <code>LV</code> refers.
	 *
	 * Question: Why are we doing this complicated replacement and do not replace <code>++LV</code> by
	 * <code>LV + 1</code> ? Answer: We want to be ready for dealing with cases where there are several pre/post
	 * increment/decrement operations in one expression. We might extend our implementation in a way where the operation
	 * is done at a certain sequence point or all evaluation orders are considered.
	 */
	public Result handlePrefixIncrementAndDecrement(final int prefixOp, final ILocation loc, ExpressionResult exprRes,
			final IASTNode hook, final Function<ExpressionResult, ExpressionResult> funMakeAssignment) {
		assert !exprRes.getLrValue().isBoogieBool();
		exprRes = mExprResultTransformer.switchToRValue(exprRes, loc, hook);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllExceptLrValue(exprRes);

		// In this case we need a temporary variable for the new value
		final AuxVarInfo auxvar =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, exprRes.getLrValue().getCType(), SFO.AUXVAR.PRE_MOD);
		builder.addAuxVarWithDeclaration(auxvar);

		final int op;
		if (prefixOp == IASTUnaryExpression.op_prefixIncr) {
			op = IASTBinaryExpression.op_plus;
		} else if (prefixOp == IASTUnaryExpression.op_prefixDecr) {
			op = IASTBinaryExpression.op_minus;
		} else {
			throw new AssertionError("no prefix");
		}

		final CType oType = exprRes.getLrValue().getCType().getUnderlyingType();
		// in-/decremented value
		final Expression valueXcremented =
				constructXcrementedValue(loc, builder, oType, op, exprRes.getLrValue().getValue());

		// assign the old value to the temporary variable
		final LeftHandSide[] tmpAsLhs = new LeftHandSide[] { auxvar.getLhs() };
		final Expression[] newValue = new Expression[] { valueXcremented };
		builder.addStatement(StatementFactory.constructAssignmentStatement(loc, tmpAsLhs, newValue));

		builder.setLrValue(new RValue(valueXcremented, oType, false, false));
		final ExpressionResult assign = funMakeAssignment.apply(builder.build());
		final RValue tmpRValue = new RValue(auxvar.getExp(), oType);
		return new ExpressionResultBuilder().addAllExceptLrValue(assign).setLrValue(tmpRValue).build();
	}

	/**
	 * Handle conditional operator according to Section 6.5.15 of C11. Assumes that opCondition, opPositive, and
	 * opNegative are the results from handling the operands. Requires that the {@link LRValue} of operands is an
	 * {@link RValue} (i.e., switchToRValueIfNecessary was applied if needed). TODO: Check all corner cases, write some
	 * testfiles.
	 *
	 */
	public ExpressionResult handleConditionalOperator(final ILocation loc, final ExpressionResult opConditionRaw,
			final ExpressionResult opPositiveRaw, final ExpressionResult opNegativeRaw, final IASTNode hook) {

		final ExpressionResult opCondition = mExprResultTransformer.rexIntToBool(opConditionRaw, loc);
		ExpressionResult opPositive = mExprResultTransformer.rexBoolToInt(opPositiveRaw, loc);
		ExpressionResult opNegative = mExprResultTransformer.rexBoolToInt(opNegativeRaw, loc);

		/*
		 * C11 6.5.15.2 The first operand shall have scalar type.
		 */
		if (!opCondition.getLrValue().getCType().isScalarType()) {
			throw new IncorrectSyntaxException(loc, "first operand of a conditional operator must have scalar type");
		}

		/*
		 * C11 6.5.15.3 One of the following shall hold for the second and third operands: <li> both operands have
		 * arithmetic type; <li> both operands have the same structure or union type; <li> both operands have void type;
		 * <li> both operands are pointers to qualified or unqualified versions of compatible types; <li> one operand is
		 * a pointer and the other is a null pointer constant; or <li> one operand is a pointer to an object type and
		 * the other is a pointer to a qualified or unqualified version of void.
		 */

		/*
		 * C11 6.5.15.4 The first operand is evaluated; there is a sequence point between its evaluation and the
		 * evaluation of the second or third operand (whichever is evaluated). The second operand is evaluated only if
		 * the first compares unequal to 0; the third operand is evaluated only if the first compares equal to 0; the
		 * result is the value of the second or third operand (whichever is evaluated), converted to the type described
		 * below. 110)
		 *
		 * --> we translate this by a Boogie if-statement, such that the side effects of the evaluation of each C
		 * expression go into the respective branch of the Boogie if statement.
		 */

		/*
		 * C11 6.5.15.5 If both the second and third operands have arithmetic type, the result type that would be
		 * determined by the usual arithmetic conversions, were they applied to those two operands, is the type of the
		 * result. If both the operands have structure or union type, the result has that type. If both operands have
		 * void type, the result has void type.
		 */

		/*
		 * C11 6.5.15.6 If both the second and third operands are pointers or one is a null pointer constant and the
		 * other is a pointer, the result type is a pointer to a type qualified with all the type qualifiers of the
		 * types referenced by both operands. Furthermore, if both operands are pointers to compatible types or to
		 * differently qualified versions of compatible types, the result type is a pointer to an appropriately
		 * qualified version of the composite type; if one operand is a null pointer constant, the result has the type
		 * of the other operand; otherwise, one operand is a pointer to void or a qualified version of void, in which
		 * case the result type is a pointer to an appropriately qualified version of void.
		 *
		 * TODO: this is only partially implemented, for example we are not doing anything about the qualifiers,
		 * currently.
		 */

		/*
		 * Treatment of the cases where one or both branches have void type and the LRValue of the dispatch result of
		 * the branch is is null: We give a dummy LRValue, whose BoogieType is a type error so it cannot be used
		 * further.
		 */
		boolean secondArgIsVoid = false;
		boolean thirdArgIsVoid = false;
		if (!opPositive.hasLRValue() || !opNegative.hasLRValue()) {
			final RValue rVal =
					new RValue(ExpressionFactory.createVoidDummyExpression(loc), new CPrimitive(CPrimitives.VOID));
			if (!opPositive.hasLRValue()) {
				opPositive = new ExpressionResultBuilder(opPositive).setLrValue(rVal).build();
				secondArgIsVoid = true;
			}
			if (!opNegative.hasLRValue()) {
				opNegative = new ExpressionResultBuilder(opNegative).setLrValue(rVal).build();
				thirdArgIsVoid = true;
			}
		}

		final CType resultCType;
		if (opPositive.getLrValue().getCType().isArithmeticType()
				&& opNegative.getLrValue().getCType().isArithmeticType()) {
			/*
			 * C11 6.5.15.5: If both the second and third operands have arithmetic type, the result type that would be
			 * determined by the usual arithmetic conversions, were they applied to those two operands, is the type of
			 * the result.
			 */
			final Pair<ExpressionResult, ExpressionResult> newOps =
					mExprResultTransformer.usualArithmeticConversions(loc, opPositive, opNegative);
			opPositive = newOps.getFirst();
			opNegative = newOps.getSecond();
			resultCType = opPositive.getLrValue().getCType();
		} else if (secondArgIsVoid && thirdArgIsVoid) {
			/* C11 6.5.15.5 If both operands have void type, the result has void type. */
			resultCType = new CPrimitive(CPrimitives.VOID);
		} else if (opPositive.getLrValue().isNullPointerConstant()
				|| opPositive.getLrValue().getCType().getUnderlyingType().isIntegerType()) {
			// TODO 2018-11-17 Matthias: I could not find a reference in the C standard that
			// allows the second disjunct above. Maybe a GNU extension?
			// However this seems to help on a bunch of SV-COMP benchmarks where we have an
			// Integer and String literal as second and third operand of the conditional
			// operator.
			/* C11 6.5.15.6 if one operand is a null pointer constant, the result has the type of the other operand; */
			if (opNegative.getLrValue().getCType().getUnderlyingType() instanceof CPointer) {
				opPositive = mExprResultTransformer.convertNullPointerConstantToPointer(opPositive,
						opNegative.getLrValue().getCType().getUnderlyingType(), loc);
				resultCType = opNegative.getLrValue().getCType();
			} else if (opNegative.getLrValue().getCType().getUnderlyingType() instanceof CArray) {
				/* if one of the branches has pointer type and one has array type, the array decays to a pointer. */
				opNegative = mExprResultTransformer.decayArrayToPointer(opNegative, loc, hook);
				opPositive = mExprResultTransformer.convertNullPointerConstantToPointer(opPositive,
						opNegative.getLrValue().getCType().getUnderlyingType(), loc);
				resultCType = opNegative.getLrValue().getCType();
			} else {
				resultCType = opNegative.getLrValue().getCType();
			}

		} else if (opNegative.getLrValue().isNullPointerConstant()
				|| opNegative.getLrValue().getCType().getUnderlyingType().isIntegerType()) {
			// TODO 2018-11-17 Matthias: I could not find a reference in the C standard that
			// allows the second disjunct above. Maybe a GNU extension?
			// However this seems to help on a bunch of SV-COMP benchmarks where we have an
			// Integer and String literal as second and third operand of the conditional
			// operator.
			/* C11 6.5.15.6 if one operand is a null pointer constant, the result has the type of the other operand; */
			if (opPositive.getLrValue().getCType().getUnderlyingType() instanceof CPointer) {
				opNegative = mExprResultTransformer.convertNullPointerConstantToPointer(opNegative,
						opPositive.getLrValue().getCType().getUnderlyingType(), loc);
				resultCType = opPositive.getLrValue().getCType();
			} else if (opPositive.getLrValue().getCType().getUnderlyingType() instanceof CArray) {
				/* if one of the branches has pointer type and one has array type, the array decays to a pointer. */
				opPositive = mExprResultTransformer.decayArrayToPointer(opPositive, loc, hook);
				opNegative = mExprResultTransformer.convertNullPointerConstantToPointer(opNegative,
						opPositive.getLrValue().getCType().getUnderlyingType(), loc);
				resultCType = opPositive.getLrValue().getCType();
			} else {
				resultCType = opPositive.getLrValue().getCType();
			}
		} else if (opPositive.getLrValue().getCType().getUnderlyingType() instanceof CArray
				&& opNegative.getLrValue().getCType().getUnderlyingType() instanceof CArray) {
			// TODO 2018-11-04 Matthias: I could not find a reference for the
			// following, but it seems to work for SV-COMP examples
			// if both operands are arrays we decay both to pointers
			resultCType = new CPointer(((CArray) opPositive.getLrValue().getCType()).getValueType());
			opPositive = mExprResultTransformer.decayArrayToPointer(opPositive, loc, hook);
			opNegative = mExprResultTransformer.decayArrayToPointer(opNegative, loc, hook);
		} else {
			// default case: the types of the operands (should) match --> we choose one of them as the result CType
			resultCType = opPositive.getLrValue().getCType();
		}
		return constructResultForConditionalOperator(loc, opCondition, opPositive, opNegative, resultCType,
				secondArgIsVoid, thirdArgIsVoid);
	}

	/**
	 * Takes preprocessing from {@link CExpressionTranslator#handleConditionalOperator}
	 */
	private ExpressionResult constructResultForConditionalOperator(final ILocation loc,
			final ExpressionResult opCondition, final ExpressionResult opPositive, final ExpressionResult opNegative,
			final CType resultCType, final boolean secondArgIsVoid, final boolean thirdArgIsVoid) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		// TODO: a solution that checks if the void value is ever assigned would be nice, but unclear if necessary
		// /*
		// * the value of this aux var may never be used outside the translation of this conditional operator.
		// * Using the aux var in the hope of detecting such errors easier. Otherwise one could just not make the
		// * assignment.
		// */

		if (opPositive.getStatements().isEmpty() && opNegative.getStatements().isEmpty()) {
			// neither second nor third operand have side-effects, we can translate to
			// a Boogie if-then-else expression
			resultBuilder.addAllExceptLrValue(opCondition, opPositive, opNegative);
			if (resultCType.isVoidType()) {
				// result type is void the value is not assigned
			} else {
				final Expression ite =
						ExpressionFactory.constructIfThenElseExpression(loc, opCondition.getLrValue().getValue(),
								opPositive.getLrValue().getValue(), opNegative.getLrValue().getValue());
				resultBuilder.setLrValue(new RValue(ite, resultCType));
			}
		} else {
			// Second or third operand has side-effects, we have to translate to an
			// if-then-else statement to make sure that side-effect are only execute if the
			// respective branch is taken.

			resultBuilder.addAllExceptLrValue(opCondition);

			// auxvar that will hold the result of the ite expression
			final AuxVarInfo auxvar;
			if (resultCType.isVoidType()) {
				/*
				 * in this case we will not make any assignment, so we do not need the aux var
				 */
				auxvar = null;
			} else {
				auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultCType, SFO.AUXVAR.ITE);
				resultBuilder.addAuxVarWithDeclaration(auxvar);
			}

			final List<Statement> ifStatements = new ArrayList<>();
			final List<Statement> elseStatements = new ArrayList<>();
			assignAuxVar(loc, opPositive, resultBuilder, auxvar, ifStatements, secondArgIsVoid);
			assignAuxVar(loc, opNegative, resultBuilder, auxvar, elseStatements, thirdArgIsVoid);
			final Statement rtrStatement = new IfStatement(loc, opCondition.getLrValue().getValue(),
					ifStatements.toArray(new Statement[ifStatements.size()]),
					elseStatements.toArray(new Statement[elseStatements.size()]));
			for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
				overapprItem.annotate(rtrStatement);
			}
			resultBuilder.addStatement(rtrStatement);
			if (resultCType.isVoidType()) {
				// result type is void the value is not assigned
			} else {
				resultBuilder.setLrValue(new RValue(auxvar.getExp(), resultCType));
			}
		}

		return resultBuilder.build();
	}

	/**
	 * Increment or decrement an expression. Construct expression that represents the value of the input expression but
	 * is incremented or decremented by one. If op is IASTBinaryExpression.op_plus we increment, if op is
	 * IASTBinaryExpression.op_minus we decrement. If ctype is CPrimitive, we increment/decrement by one and also call
	 * the method that adds (depending on the settings) an overflow check. If ctype is CPointer, we increment/decrement
	 * by the size of the pointsToType and call the method that adds (depending on the settings) an check if the pointer
	 * arithmetic was legal.
	 *
	 * @param result
	 *            note that this method has sideeffects on this object! (add..BoundCheck(..) calls)
	 */
	private Expression constructXcrementedValue(final ILocation loc, final ExpressionResultBuilder result,
			final CType ctype, final int op, final Expression value) {
		assert op == IASTBinaryExpression.op_plus
				|| op == IASTBinaryExpression.op_minus : "has to be either minus or plus";
		final Expression valueIncremented;
		if (ctype instanceof CPointer) {
			final CPointer cPointer = (CPointer) ctype;
			final Expression oneEpr = mTypeSizes.constructLiteralForIntegerType(loc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
			final CPrimitive oneType = mExpressionTranslation.getCTypeOfPointerComponents();
			final RValue one = new RValue(oneEpr, oneType);
			valueIncremented = mMemoryHandler.doPointerArithmetic(op, loc, value, one, cPointer.getPointsToType());
			addOffsetInBoundsCheck(loc, valueIncremented, result);
		} else if (ctype instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) ctype;

			final Expression one;
			if (ctype.isFloatingType()) {
				one = mExpressionTranslation.constructLiteralForFloatingType(loc, cPrimitive, BigDecimal.ONE);
			} else {
				one = mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ONE);
			}
			addIntegerBoundsCheck(loc, result, cPrimitive, op, value, one);
			valueIncremented =
					mExpressionTranslation.constructArithmeticExpression(loc, op, value, cPrimitive, one, cPrimitive);
		} else {
			throw new IllegalArgumentException("input has to be CPointer or CPrimitive");
		}
		return valueIncremented;
	}

	/**
	 * Add to divisorExpRes a check if divisior is zero.
	 */
	private ExpressionResult addDivisionByZeroCheck(final ILocation loc, final ExpressionResult divisorExpRes) {
		final Expression divisor = divisorExpRes.getLrValue().getValue();
		final CPrimitive divisorType = (CPrimitive) divisorExpRes.getLrValue().getCType();

		final PointerCheckMode checkMode;
		if (divisorType.isIntegerType()) {
			checkMode = mSettings.getDivisionByZeroOfIntegerTypes();
		} else if (divisorType.isFloatingType()) {
			checkMode = mSettings.getDivisionByZeroOfFloatingTypes();
		} else {
			throw new UnsupportedOperationException("cannot check division by zero for type " + divisorType);
		}

		if (checkMode == PointerCheckMode.IGNORE) {
			return divisorExpRes;
		}

		final Expression divisorNotZero;
		if (divisorType.isIntegerType()) {
			final Expression zero = mTypeSizes.constructLiteralForIntegerType(loc, divisorType, BigInteger.ZERO);
			divisorNotZero = mExpressionTranslation.constructBinaryEqualityExpression(loc,
					IASTBinaryExpression.op_notequals, divisor, divisorType, zero, divisorType);
		} else if (divisorType.isFloatingType()) {
			final Expression zero =
					mExpressionTranslation.constructLiteralForFloatingType(loc, divisorType, BigDecimal.ZERO);
			divisorNotZero = mExpressionTranslation.constructBinaryComparisonFloatingPointExpression(loc,
					IASTBinaryExpression.op_notequals, divisor, divisorType, zero, divisorType);
		} else {
			throw new UnsupportedOperationException("cannot check division by zero for type " + divisorType);
		}

		final Statement additionalStatement;
		if (checkMode == PointerCheckMode.ASSUME) {
			additionalStatement = new AssumeStatement(loc, divisorNotZero);
		} else if (checkMode == PointerCheckMode.ASSERTandASSUME) {
			additionalStatement = new AssertStatement(loc, divisorNotZero);
			final Check check = new Check(Spec.DIVISION_BY_ZERO);
			check.annotate(additionalStatement);
		} else {
			throw new AssertionError("illegal");
		}
		return new ExpressionResultBuilder(divisorExpRes).addStatement(additionalStatement).build();
	}

	/**
	 * Construct {@link Expression} that compares a component of two pointers.
	 *
	 * @param loc
	 * @param op
	 *            Comparison operation.
	 * @param leftPointer
	 *            Boogie expression that represents pointer.
	 * @param rightPointer
	 *            Boogie expression that represents pointer.
	 * @param component
	 *            Defines which component is compared. Either "base" or "offset"
	 */
	private Expression constructPointerComponentRelation(final ILocation loc, final int op,
			final Expression leftPointer, final Expression rightPointer, final String component) {
		assert component.equals(SFO.POINTER_BASE) || component.equals(SFO.POINTER_OFFSET) : "unknown pointer component";
		final StructAccessExpression leftComponent =
				ExpressionFactory.constructStructAccessExpression(loc, leftPointer, component);
		final StructAccessExpression rightComponent =
				ExpressionFactory.constructStructAccessExpression(loc, rightPointer, component);
		switch (op) {
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			return mExpressionTranslation.constructBinaryEqualityExpression(loc, op, leftComponent,
					mExpressionTranslation.getCTypeOfPointerComponents(), rightComponent,
					mExpressionTranslation.getCTypeOfPointerComponents());
		}
		case IASTBinaryExpression.op_lessThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_greaterEqual:
			return mExpressionTranslation.constructBinaryComparisonExpression(loc, op, leftComponent,
					mExpressionTranslation.getCTypeOfPointerComponents(), rightComponent,
					mExpressionTranslation.getCTypeOfPointerComponents());
		default:
			throw new IllegalArgumentException("op " + op);
		}
	}

	/**
	 * Add checks for integer overflows. Construct arithmetic operation and add an assert statement that checks if the
	 * result is in the range of the corresponding C data type (i.e. check for overflow wrt. max and min value). Note
	 * that we do not check if a given expression is in the range. We explicitly construct a new expression for the
	 * arithmetic operation in this check because we possibly have to adjust the data type used in boogie. E.g., if we
	 * use 32bit bitvectors in Boogie we are unable to express an overflow check for a 32bit integer addition in C.
	 * Instead, we have to use a 33bit bit bitvector in Boogie.
	 */
	private void addIntegerBoundsCheck(final ILocation loc, final ExpressionResultBuilder erb,
			final CPrimitive resultType, final int operation, final Expression... operands) {

		if (!mSettings.checkSignedIntegerBounds() || !resultType.isIntegerType() || mTypeSizes.isUnsigned(resultType)) {
			// nothing to do
			return;
		}
		final Pair<Expression, Expression> inBoundsCheck;
		if (operands.length == 1) {
			assert operation == IASTUnaryExpression.op_minus;
			inBoundsCheck = mExpressionTranslation.constructOverflowCheckForUnaryExpression(loc, operation, resultType,
					operands[0]);

		} else if (operands.length == 2) {
			inBoundsCheck = mExpressionTranslation.constructOverflowCheckForArithmeticExpression(loc, operation,
					resultType, operands[0], operands[1]);
		} else {
			throw new AssertionError("no such operation");
		}
		addOverflowAssertion(loc, inBoundsCheck.getFirst(), erb);
		addOverflowAssertion(loc, inBoundsCheck.getSecond(), erb);
	}

	// TODO: Is this the right place for this method?
	public static void addOverflowAssertion(final ILocation loc, final Expression condition,
			final ExpressionResultBuilder erb) {
		if (ExpressionFactory.isTrueLiteral(condition)) {
			// Avoid the creation of "assert true" statements
			return;
		}
		final AssertStatement assertSt = new AssertStatement(loc, condition);
		new Check(Spec.INTEGER_OVERFLOW).annotate(assertSt);
		erb.addStatement(assertSt);
	}

	/**
	 * Check if two pointers have the same base component (i.e. if both point to the same array object). Depending on
	 * the preferences of this plugin we
	 * <ul>
	 * <li>assert that both have the same base component,
	 * <li>assume that both have the same base component, or
	 * <li>add nothing.
	 * </ul>
	 *
	 * @param leftPtr
	 *            Boogie {@link Expression} that represents the left pointer.
	 * @param rightPtr
	 *            Boogie {@link Expression} that represents the right pointer.
	 * @param erb
	 *            {@link ExpressionResultBuilder} to which the additional statements are added.
	 */
	private ExpressionResultBuilder addBaseEqualityCheck(final ILocation loc, final Expression leftPtr,
			final Expression rightPtr, final ExpressionResultBuilder erb) {

		if (mSettings.getPointerSubtractionAndComparisonValidityCheckMode() == PointerCheckMode.IGNORE) {
			// do not check anything
			return erb;
		}
		final Expression baseEquality = constructPointerComponentRelation(loc, IASTBinaryExpression.op_equals, leftPtr,
				rightPtr, SFO.POINTER_BASE);
		switch (mSettings.getPointerSubtractionAndComparisonValidityCheckMode()) {
		case ASSERTandASSUME:
			final Statement assertStm = new AssertStatement(loc, baseEquality);
			final Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
			chk.annotate(assertStm);
			erb.addStatement(assertStm);
			return erb;
		case ASSUME:
			final Statement assumeStm = new AssumeStatement(loc, baseEquality);
			erb.addStatement(assumeStm);
			return erb;
		case IGNORE:
			throw new AssertionError("case handled before");
		default:
			throw new AssertionError("unknown value");
		}
	}

	/**
	 * Subtract two pointers.
	 *
	 * @param pointsToType
	 *            {@link CType} of the objects to which the pointers point.
	 * @param leftPtr
	 *            Boogie {@link Expression} that represents the left pointer.
	 * @param rightPtr
	 *            Boogie {@link Expression} that represents the right pointer.
	 *
	 * @return An {@link Expression} that represents the difference of two Pointers according to C11 6.5.6.9.
	 */
	private Expression doPointerSubtraction(final ILocation loc, final Expression ptr1, final Expression ptr2,
			final CType pointsToType) {
		final Expression ptr1Offset = ExpressionFactory.constructStructAccessExpression(loc, ptr1, SFO.POINTER_OFFSET);
		final Expression ptr2Offset = ExpressionFactory.constructStructAccessExpression(loc, ptr2, SFO.POINTER_OFFSET);
		final Expression offsetDifference = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_minus, ptr1Offset, mExpressionTranslation.getCTypeOfPointerComponents(),
				ptr2Offset, mExpressionTranslation.getCTypeOfPointerComponents());
		final Expression typesize = mMemoryHandler.calculateSizeOf(loc, pointsToType);
		final CPrimitive typesizeType = mExpressionTranslation.getCTypeOfPointerComponents();
		final Expression offsetDifferenceDividedByTypesize =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_divide,
						offsetDifference, mExpressionTranslation.getCTypeOfPointerComponents(), typesize, typesizeType);
		return offsetDifferenceDividedByTypesize;
	}

	/**
	 * Checks if an {@link RValue} is an Integer of value 0
	 */
	private boolean isNullPointerEquivalent(final RValue value) {
		return BigInteger.ZERO.equals(mTypeSizes.extractIntegerValue(value));
	}

	/**
	 * Check if pointer offset is in a legal range. In case a pointer points to allocated memory, the "base" of a
	 * pointer points to some array object (in C). Now we check if the offset of this pointer does not violate the
	 * bounds of that array. This means that the offset
	 * <ul>
	 * <li>must be non-negative, and
	 * <li>must be small enough that the pointer points to an element of the array or one past the last element of the
	 * array.
	 * </ul>
	 * Depending on the preferences of this plugin we
	 * <ul>
	 * <li>assert that the offset is in the bounds of the array,
	 * <li>assume that the offset is in the bounds of the array, or
	 * <li>add nothing.
	 * </ul>
	 *
	 * @param ptr
	 *            Boogie {@link Expression} that represents the pointer.
	 * @param erb
	 *            {@link ExpressionResult} to which the additional statements are added.
	 */
	private void addOffsetInBoundsCheck(final ILocation loc, final Expression ptr, final ExpressionResultBuilder erb) {
		// TODO: Matthias 2015-09-08 implement this
		// maybe additional parameters are required.
	}

	private static void assignAuxVar(final ILocation loc, final ExpressionResult branchResult,
			final ExpressionResultBuilder resultBuilder, final AuxVarInfo auxvar,
			final List<Statement> resultStatements, final boolean relevantArgIsVoid) {
		if (resultStatements != null) {
			resultStatements.addAll(branchResult.getStatements());
		}
		if (auxvar != null && !relevantArgIsVoid) {
			final LeftHandSide[] lhs = { auxvar.getLhs() };
			final Expression assignedVal = branchResult.getLrValue().getValue();
			final AssignmentStatement assignStmt =
					StatementFactory.constructAssignmentStatement(loc, lhs, new Expression[] { assignedVal });
			for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
				overapprItem.annotate(assignStmt);
			}
			resultStatements.add(assignStmt);
		}
		resultBuilder.addAllExceptLrValueAndStatements(branchResult);

	}

}
