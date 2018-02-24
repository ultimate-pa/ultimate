/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeCheckHelper;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Construct Boogie Expressions (and LeftHandSides), use this instead of the constructors.
 * Functionalities:
 * <li> do minor simplifications (e.g. if all operands are literals)
 * <li> computes types for the resulting Boogie expressions, throws an exception if it cannot be typed.
 *   Note that this means that all input Boogie expressions must have a type. (Which is the case if they have been
 *   constructed using this factory.)
 *
 * @author Daniel Dietsch
 * @author Matthias Heizmann
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ExpressionFactory {


	/**
	 * Name for dummy expressions that represent a "void" result. Those identifier expressions may not be used anywhere
	 * and thus should get an error BoogieType.
	 */
	public static final String DUMMY_VOID = null;


	public static Expression constructUnaryExpression(final ILocation loc, final UnaryExpression.Operator operator,
			final Expression expr) {
		final Expression exprLiteral = filterLiteral(expr);

		final BoogieType resultType =
				TypeCheckHelper.typeCheckUnaryExpression(operator, (BoogieType) expr.getType(),
						new TypeErrorReporter(loc));

		Expression result;
		if (exprLiteral != null) {
			switch (operator) {
			case ARITHNEGATIVE:
				if (exprLiteral instanceof IntegerLiteral) {
					final BigInteger value = new BigInteger(((IntegerLiteral) exprLiteral).getValue());
					result = createIntegerLiteral(loc, (value.negate()).toString());
				} else if (exprLiteral instanceof RealLiteral) {
					final BigDecimal value = new BigDecimal(((RealLiteral) exprLiteral).getValue());
					result = createRealLiteral(loc, (value.negate()).toString());
				} else {
					throw new IllegalArgumentException("type error: unable to apply " + operator);
				}
				break;
			case LOGICNEG:
				if (exprLiteral instanceof BooleanLiteral) {
					final boolean value = ((BooleanLiteral) exprLiteral).getValue();
					result = createBooleanLiteral(loc, !value);
				} else {
					throw new IllegalArgumentException("type error: unable to apply " + operator);
				}
				break;
			case OLD:
				result = expr;
			default:
				throw new AssertionError("unknown operator " + operator);
			}
		} else {
			result = new UnaryExpression(loc, resultType, operator, expr);
		}
		return result;
	}

	public static Expression newBinaryExpression(final ILocation loc, final Operator operator, final Expression left,
			final Expression right) {
		final Expression leftLiteral = filterLiteral(left);
		final Expression rightLiteral = filterLiteral(right);
		Expression result;
		if ((leftLiteral != null) && (rightLiteral != null)) {
			assert leftLiteral.getClass().equals(rightLiteral.getClass()) : "incompatible literals: "
					+ leftLiteral.getClass() + " and " + rightLiteral.getClass();
			if (leftLiteral instanceof BooleanLiteral) {
				result = constructBinaryExpression_Bool(loc, operator, (BooleanLiteral) leftLiteral,
						(BooleanLiteral) rightLiteral);
			} else if (leftLiteral instanceof IntegerLiteral) {
				result = constructBinaryExpression_Integer(loc, operator, (IntegerLiteral) leftLiteral,
						(IntegerLiteral) rightLiteral);
			} else if (leftLiteral instanceof RealLiteral) {
				result = constructBinaryExpression_Real(loc, operator, (RealLiteral) leftLiteral,
						(RealLiteral) rightLiteral);
			} else if (leftLiteral instanceof BitvecLiteral) {
				result = constructBinaryExpression_Bitvector(loc, operator, (BitvecLiteral) leftLiteral,
						(BitvecLiteral) rightLiteral);
			} else {
				throw new AssertionError("impossible");
			}
		} else {
			result = constructBinaryExpression(loc, operator, left, right);
		}
		return result;
	}

	private static BooleanLiteral constructBinaryExpression_Bool(final ILocation loc, final Operator operator,
			final BooleanLiteral leftLiteral, final BooleanLiteral rightLiteral) {
		final boolean leftValue = leftLiteral.getValue();
		final boolean rightValue = rightLiteral.getValue();
		final boolean result;
		switch (operator) {
		case ARITHDIV:
		case ARITHMINUS:
		case ARITHMOD:
		case ARITHMUL:
		case ARITHPLUS:
		case BITVECCONCAT:
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT:
		case COMPPO:
			throw new IllegalArgumentException("type error: unable to apply " + operator + " to bool");
		case COMPEQ:
			result = (leftValue == rightValue);
			break;
		case COMPNEQ:
			result = (leftValue != rightValue);
			break;
		case LOGICAND:
			result = leftValue && rightValue;
			break;
		case LOGICIFF:
			result = (leftValue == rightValue);
			break;
		case LOGICIMPLIES:
			result = (!leftValue || rightValue);
			break;
		case LOGICOR:
			result = leftValue || rightValue;
			break;
		default:
			throw new AssertionError("unknown operator " + operator);
		}
		return createBooleanLiteral(loc, result);
	}

	private static Expression constructBinaryExpression_Integer(final ILocation loc, final Operator operator,
			final IntegerLiteral leftLiteral, final IntegerLiteral rightLiteral) {
		final BigInteger leftValue = new BigInteger(leftLiteral.getValue());
		final BigInteger rightValue = new BigInteger(rightLiteral.getValue());
		switch (operator) {
		case ARITHDIV: {
			final BigInteger result = BoogieUtils.euclideanDiv(leftValue, rightValue);
			return createIntegerLiteral(loc, result.toString());
		}
		case ARITHMINUS: {
			final BigInteger result = leftValue.subtract(rightValue);
			return createIntegerLiteral(loc, result.toString());
		}
		case ARITHMOD: {
			final BigInteger result = BoogieUtils.euclideanMod(leftValue, rightValue);
			return createIntegerLiteral(loc, result.toString());
		}
		case ARITHMUL: {
			final BigInteger result = leftValue.multiply(rightValue);
			return createIntegerLiteral(loc, result.toString());
		}
		case ARITHPLUS: {
			final BigInteger result = leftValue.add(rightValue);
			return createIntegerLiteral(loc, result.toString());
		}
		case COMPEQ: {
			final boolean result = (leftValue.compareTo(rightValue) == 0);
			return createBooleanLiteral(loc, result);
		}
		case COMPGEQ: {
			final boolean result = (leftValue.compareTo(rightValue) >= 0);
			return createBooleanLiteral(loc, result);
		}
		case COMPGT: {
			final boolean result = (leftValue.compareTo(rightValue) > 0);
			return createBooleanLiteral(loc, result);
		}
		case COMPLEQ: {
			final boolean result = (leftValue.compareTo(rightValue) <= 0);
			return createBooleanLiteral(loc, result);
		}
		case COMPLT: {
			final boolean result = (leftValue.compareTo(rightValue) < 0);
			return createBooleanLiteral(loc, result);
		}
		case COMPNEQ: {
			final boolean result = (leftValue.compareTo(rightValue) != 0);
			return createBooleanLiteral(loc, result);
		}
		case BITVECCONCAT:
		case COMPPO:
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR:
			throw new IllegalArgumentException("type error: unable to apply " + operator + " to bool");
		default:
			throw new AssertionError("unknown operator " + operator);
		}
	}

	private static Expression constructBinaryExpression_Real(final ILocation loc, final Operator operator,
			final RealLiteral leftLiteral, final RealLiteral rightLiteral) {
		final BigDecimal leftValue = new BigDecimal(leftLiteral.getValue());
		final BigDecimal rightValue = new BigDecimal(rightLiteral.getValue());
		switch (operator) {
		case ARITHDIV: {
			final BigDecimal result = leftValue.divide(rightValue);
			return new RealLiteral(loc, result.toString());
		}
		case ARITHMINUS: {
			final BigDecimal result = leftValue.subtract(rightValue);
			return new RealLiteral(loc, result.toString());
		}
		case ARITHMUL: {
			final BigDecimal result = leftValue.multiply(rightValue);
			return new RealLiteral(loc, result.toString());
		}
		case ARITHPLUS: {
			final BigDecimal result = leftValue.add(rightValue);
			return new RealLiteral(loc, result.toString());
		}
		case COMPEQ: {
			final boolean result = (leftValue.compareTo(rightValue) >= 0);
			return createBooleanLiteral(loc, result);
		}
		case COMPGEQ: {
			final boolean result = (leftValue.compareTo(rightValue) >= 0);
			return createBooleanLiteral(loc, result);
		}
		case COMPGT: {
			final boolean result = (leftValue.compareTo(rightValue) >= 0);
			return createBooleanLiteral(loc, result);
		}
		case COMPLEQ: {
			final boolean result = (leftValue.compareTo(rightValue) >= 0);
			return createBooleanLiteral(loc, result);
		}
		case COMPLT: {
			final boolean result = (leftValue.compareTo(rightValue) >= 0);
			return createBooleanLiteral(loc, result);
		}
		case COMPNEQ: {
			final boolean result = (leftValue.compareTo(rightValue) >= 0);
			return createBooleanLiteral(loc, result);
		}
		case ARITHMOD:
		case BITVECCONCAT:
		case COMPPO:
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR:
			throw new IllegalArgumentException("type error: unable to apply " + operator + " to bool");
		default:
			throw new AssertionError("unknown operator " + operator);
		}
	}

	private static Expression constructBinaryExpression_Bitvector(final ILocation loc, final Operator operator,
			final BitvecLiteral leftLiteral, final BitvecLiteral rightLiteral) {
		final BigInteger leftValue = new BigInteger(leftLiteral.getValue());
		final BigInteger rightValue = new BigInteger(rightLiteral.getValue());
		if (leftValue.compareTo(BigInteger.ZERO) < 0) {
			throw new IllegalArgumentException("assumed non-negative number here!");
		}
		if (rightValue.compareTo(BigInteger.ZERO) < 0) {
			throw new IllegalArgumentException("assumed non-negativenumber here!");
		}
		final int leftLength = leftLiteral.getLength();
		final int rightLength = rightLiteral.getLength();

		switch (operator) {
		case COMPEQ: {
			if (leftLength != rightLength) {
				throw new IllegalArgumentException("type error: cannot compare bitvectors of differnt lengths");
			}
			final boolean result = (leftValue.equals(rightValue));
			return createBooleanLiteral(loc, result);
		}
		case COMPNEQ: {
			if (leftLength != rightLength) {
				throw new IllegalArgumentException("type error: cannot compare bitvectors of differnt lengths");
			}
			final boolean result = !(leftValue.equals(rightValue));
			return createBooleanLiteral(loc, result);
		}
		case BITVECCONCAT: {
			throw new UnsupportedOperationException("not yet implemented " + operator);
		}
		case ARITHDIV:
		case ARITHMINUS:
		case ARITHMOD:
		case ARITHMUL:
		case ARITHPLUS:
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT:
		case COMPPO:
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR:
			throw new IllegalArgumentException("type error: unable to apply " + operator + " to bool");
		default:
			throw new AssertionError("unknown operator " + operator);
		}
	}

	public static Expression constructIfThenElseExpression(final ILocation loc, final Expression condition,
			final Expression thenPart, final Expression elsePart) {
		final Expression condLiteral = filterLiteral(condition);
		if (condLiteral instanceof BooleanLiteral) {
			final boolean value = ((BooleanLiteral) condLiteral).getValue();
			if (value) {
				return thenPart;
			}
			return elsePart;
		}
		final BoogieType type = TypeCheckHelper.typeCheckIfThenElseExpression((BoogieType) condition.getType(),
				(BoogieType) thenPart.getType(), (BoogieType) elsePart.getType(), new TypeErrorReporter(loc));
		return new IfThenElseExpression(loc, type, condition, thenPart, elsePart);

	}

	private static Expression filterLiteral(final Expression expr) {
		if ((expr instanceof IntegerLiteral) || (expr instanceof BooleanLiteral) || (expr instanceof BitvecLiteral)
				|| (expr instanceof RealLiteral)) {
			return expr;
		}
		return null;
	}

	public static boolean isTrueLiteral(final Expression expr) {
		if (expr instanceof BooleanLiteral) {
			final BooleanLiteral bl = (BooleanLiteral) expr;
			if (bl.getValue()) {
				return true;
			}
		}
		return false;
	}

	/**
	 *
	 * @param loc
	 * @param operand
	 * @param high
	 *            exclusive
	 * @param low
	 *            inclusive
	 * @return
	 */
	public static Expression constructBitvectorAccessExpression(final ILocation loc, final Expression operand,
			final int high, final int low) {

		final BoogieType type = TypeCheckHelper.typeCheckBitVectorAccessExpression(
					TypeCheckHelper.getBitVecLength((BoogieType) operand.getType()), high,
					low, (BoogieType) operand.getType(), new TypeErrorReporter(loc));

		final Expression operandLiteral = filterLiteral(operand);
		if (operandLiteral instanceof BitvecLiteral) {
			final BigInteger biValue = new BigInteger(((BitvecLiteral) operandLiteral).getValue());
			final BigInteger two = BigInteger.valueOf(2);
			final BigInteger dividedByLow = biValue.divide(two.pow(low));
			final BigInteger biresult = dividedByLow.mod(two.pow(high));
			return new BitvecLiteral(loc, type, biresult.toString(), high - low);
		}
		return new BitVectorAccessExpression(loc, type, operand, high, low);
	}

	public static Expression and(final ILocation loc, final List<Expression> exprs) {
		return bin(loc, exprs, true, Operator.LOGICAND);
	}

	public static Expression or(final ILocation loc, final List<Expression> exprs) {
		return bin(loc, exprs, false, Operator.LOGICOR);
	}

	private static Expression bin(final ILocation loc, final List<Expression> exprs, final boolean neutralElement,
			final Operator op) {
		if (exprs == null || exprs.isEmpty()) {
			return createBooleanLiteral(loc, neutralElement);
		}
		if (exprs.size() == 1) {
			return exprs.get(0);
		}

		final Iterator<Expression> iter = exprs.iterator();
		Expression current = iter.next();
		while (iter.hasNext()) {
			current = new BinaryExpression(loc, op, current, iter.next());
		}
		return current;
	}

	public static StructConstructor constructStructConstructor(final ILocation loc, final String[] fieldIds,
			final Expression[] fieldValues) {
		assert fieldIds.length == fieldValues.length;
		final BoogieType[] fieldTypes = new BoogieType[fieldIds.length];
		boolean hasError = false;
		for (int i = 0; i < fieldIds.length; i++) {
			fieldTypes[i] = (BoogieType) fieldValues[i].getType();
			hasError |= fieldValues[i].getType().equals(BoogieType.TYPE_ERROR);
		}
		final BoogieType type = hasError ? BoogieType.TYPE_ERROR :
			BoogieType.createStructType(fieldIds, fieldTypes);
		return new StructConstructor(loc, type, fieldIds, fieldValues);
	}

	public static StructLHS constructStructAccessLhs(final ILocation loc, final LeftHandSide struct,
			final String fieldName) {
		final BoogieType lhsType = TypeCheckHelper.typeCheckStructAccessExpressionOrLhs((BoogieType) struct.getType(),
				fieldName, new TypeErrorReporter(loc));
		return new StructLHS(loc, lhsType, struct, fieldName);
	}

	public static ArrayAccessExpression constructNestedArrayAccessExpression(final ILocation loc,
			final Expression array, final Expression[] indices) {
		if (indices.length == 0) {
			throw new AssertionError("attempting to build array access without indices");
		}

		if (indices.length == 1) {
			final BoogieArrayType arrayType = (BoogieArrayType) array.getType();
			final List<BoogieType> indicesTypes = Arrays.stream(indices)
					.map(exp -> (BoogieType) exp.getType()).collect(Collectors.toList());
			final BoogieType newType = TypeCheckHelper.typeCheckArrayAccessExpressionOrLhs(arrayType, indicesTypes,
					new TypeErrorReporter(loc));
			return new ArrayAccessExpression(loc, newType, array, indices);
		}
		final Expression[] innerIndices = Arrays.copyOfRange(indices, 0, indices.length - 1);
		final Expression innerArrayAccessExpression = constructNestedArrayAccessExpression(loc, array, innerIndices);

		final Expression outerMostIndexValue = indices[indices.length - 1];
		final Expression[] outerMostIndex = new Expression[] { outerMostIndexValue };

		final BoogieArrayType arrayType = (BoogieArrayType) innerArrayAccessExpression.getType();
		final BoogieType newType = TypeCheckHelper.typeCheckArrayAccessExpressionOrLhs(arrayType,
					Arrays.asList(new BoogieType[] { (BoogieType) outerMostIndexValue.getType() }),
					new TypeErrorReporter(loc));

		return new ArrayAccessExpression(loc, newType, innerArrayAccessExpression, outerMostIndex);
	}

	public static ArrayLHS constructNestedArrayLHS(final ILocation loc, final LeftHandSide array,
			final Expression[] indices) {
		if (indices.length == 0) {
			throw new AssertionError("attempting to build array access without indices");
		}
		assert indices[0].getType() != null;
		assert array.getType() != null;



		if (indices.length == 1) {
			final BoogieArrayType arrayType = (BoogieArrayType) array.getType();
			final List<BoogieType> indicesTypes = Arrays.stream(indices)
					.map(exp -> (BoogieType) exp.getType()).collect(Collectors.toList());
			final BoogieType lhsType = TypeCheckHelper.typeCheckArrayAccessExpressionOrLhs(arrayType, indicesTypes,
					new TypeErrorReporter(loc));
			return new ArrayLHS(loc, lhsType, array, indices);
		}
		final Expression[] innerIndices = Arrays.copyOfRange(indices, 0, indices.length - 1);
		final LeftHandSide innerLhs = constructNestedArrayLHS(loc, array, innerIndices);

		final Expression outerMostIndexValue = indices[indices.length - 1];
		final Expression[] outerMostIndex = new Expression[] { outerMostIndexValue };

		final BoogieArrayType arrayType = (BoogieArrayType) innerLhs.getType();
//			final List<BoogieType> indicesTypes = Arrays.stream(innerIndices)
//					.map(exp -> (BoogieType) exp.getType()).collect(Collectors.toList());
			final BoogieType lhsType = TypeCheckHelper.typeCheckArrayAccessExpressionOrLhs(arrayType,
					Arrays.asList(new BoogieType[] { (BoogieType) outerMostIndexValue.getType() }),
					new TypeErrorReporter(loc));

		return new ArrayLHS(loc, lhsType, innerLhs, outerMostIndex);
	}

	public static ArrayLHS constructNestedArrayLHS(final ILocation loc, final IBoogieType type, final LeftHandSide lhs,
			final Expression[] indices) {
		return constructNestedArrayLHS(loc, lhs, indices);
	}

	public static IdentifierExpression constructIdentifierExpression(final ILocation loc, final BoogieType type,
			final String identifier, final DeclarationInformation declarationInformation) {
		assert loc != null && type != null && identifier != null && declarationInformation != null;
		return new IdentifierExpression(loc, type, identifier, declarationInformation);
	}

	public static VariableLHS constructVariableLHS(final ILocation loc, final BoogieType type,
			final String identifier, final DeclarationInformation declarationInformation) {
		assert loc != null && type != null && identifier != null && declarationInformation != null;
		return new VariableLHS(loc, type, identifier, declarationInformation);
	}

	public static ArrayStoreExpression constructArrayStoreExpression(final ILocation loc, final Expression array,
			final Expression[] indices, final Expression value) {

		final List<BoogieType> indicesTypes = new ArrayList<>();
		for (final Expression index : indices) {
			indicesTypes.add((BoogieType) index.getType());
		}

		final BoogieType type = TypeCheckHelper.typeCheckArrayStoreExpression((BoogieType) array.getType(),
				indicesTypes, (BoogieType) value.getType(), new TypeErrorReporter(loc));
		return new ArrayStoreExpression(loc, type, array, indices, value);
	}

	public static BinaryExpression constructBinaryExpression(final ILocation loc, final Operator operator,
			final Expression operand1, final Expression operand2) {
		final BoogieType type = TypeCheckHelper.typeCheckBinaryExpression(operator,
				(BoogieType) operand1.getType(),
				(BoogieType) operand2.getType(),
				new TypeErrorReporter(loc));
		return new BinaryExpression(loc, type, operator, operand1, operand2);
	}

	public static FunctionApplication constructFunctionApplication(final ILocation loc, final String identifier,
			final Expression[] arguments, final FunctionDeclaration declaration) {
		final BoogieType type = (BoogieType) declaration.getOutParam().getType().getBoogieType();
		return new FunctionApplication(loc, type, identifier, arguments);
	}

	public static StructAccessExpression constructStructAccessExpression(final ILocation loc, final Expression struct,
			final String fieldName) {
		final BoogieType type = TypeCheckHelper.typeCheckStructAccessExpressionOrLhs((BoogieType) struct.getType() ,
				fieldName, new TypeErrorReporter(loc));
		return new StructAccessExpression(loc, type, struct, fieldName);
	}

	public static BooleanLiteral createBooleanLiteral(final ILocation loc, final boolean value) {
		return new BooleanLiteral(loc, BoogieType.TYPE_BOOL, value);
	}

	public static IntegerLiteral createIntegerLiteral(final ILocation loc, final String value) {
		return new IntegerLiteral(loc, BoogieType.TYPE_INT, value);
	}

	public static BitvecLiteral createBitvecLiteral(final ILocation loc, final String value, final int length) {
		return new BitvecLiteral(loc, BoogieType.createBitvectorType(length), value, length);
	}

	public static RealLiteral createRealLiteral(final ILocation loc, final String value) {
		return new RealLiteral(loc, BoogieType.TYPE_REAL, value);
	}

	public static StringLiteral createStringLiteral(final ILocation loc, final String value) {
		// TODO: what boogie type should we give a string literal??
		return new StringLiteral(loc, value);
	}

	/**
	 * Returns an Expression that is the same as the given expression, except that its BoogieType has been changed
	 * to the given BoogieType.
	 *
	 * Note that this circumvents our type checks, thus should not be used for the final translation, as the type errors
	 * would occur in the BoogiePreprocessor.. (but is currently use in pre run mode).
	 *
	 * @param oe
	 * @param newType
	 * @return
	 */
	public static Expression replaceBoogieType(final Expression oe, final BoogieType newType) {
		return modifyExpression(oe, x -> x, x -> newType);
	}

	public static Expression modifyExpression(final Expression oe, final Function<ILocation, ILocation> oldToNewLoc,
			final Function<BoogieType, BoogieType> oldToNewType) {

		final ILocation newLoc = oldToNewLoc.apply(oe.getLoc());
		final BoogieType newType = oldToNewType.apply((BoogieType) oe.getType());

		if (oe instanceof ArrayAccessExpression) {
			return new ArrayAccessExpression(
					newLoc,
					newType,
					((ArrayAccessExpression) oe).getArray(),
					((ArrayAccessExpression) oe).getIndices());
		} else if (oe instanceof ArrayStoreExpression) {
			return new ArrayStoreExpression(
					newLoc,
					newType,
					((ArrayStoreExpression) oe).getArray(),
					((ArrayStoreExpression) oe).getIndices(),
					((ArrayStoreExpression) oe).getValue());
		} else if (oe instanceof BinaryExpression) {
			return new BinaryExpression(
					newLoc,
					newType,
					((BinaryExpression) oe).getOperator(),
					((BinaryExpression) oe).getLeft(),
					((BinaryExpression) oe).getRight());
		} else if (oe instanceof BitvecLiteral) {
			return new BitvecLiteral(
					newLoc,
					newType,
					((BitvecLiteral) oe).getValue(),
					((BitvecLiteral) oe).getLength());
		} else if (oe instanceof BitVectorAccessExpression) {
			return new BitVectorAccessExpression(
					newLoc,
					newType,
					((BitVectorAccessExpression) oe).getBitvec(),
					((BitVectorAccessExpression) oe).getStart(),
					((BitVectorAccessExpression) oe).getEnd());
//		} else if (oe instanceof BooleanLiteral) {
//			return createBooleanLiteral(newLoc, newType, ((BooleanLiteral) oe).getValue());
		} else if (oe instanceof FunctionApplication) {
			return new FunctionApplication(
					newLoc,
					newType,
					((FunctionApplication) oe).getIdentifier(),
					((FunctionApplication) oe).getArguments());
		} else if (oe instanceof IdentifierExpression) {
			return new IdentifierExpression(newLoc, newType,
					((IdentifierExpression) oe).getIdentifier(),
					((IdentifierExpression) oe).getDeclarationInformation());
		} else if (oe instanceof StructConstructor) {
			return new StructConstructor(newLoc, newType,
					((StructConstructor) oe).getFieldIdentifiers(),
					((StructConstructor) oe).getFieldValues());
			// TODO implement these if needed
//		} else if (oe instanceof IfThenElseExpression) {
//		} else if (oe instanceof IntegerLiteral) {
//		} else if (oe instanceof QuantifierExpression) {
//		} else if (oe instanceof RealLiteral) {
//		} else if (oe instanceof StringLiteral) {
//		} else if (oe instanceof StructAccessExpression) {
//		} else if (oe instanceof UnaryExpression) {
		} else {
			throw new AssertionError("unexpected expression type");
		}
	}

	public static IdentifierExpression createVoidDummyExpression(final ILocation loc) {
		return constructIdentifierExpression(loc, BoogieType.TYPE_ERROR,
				DUMMY_VOID, DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}


}
