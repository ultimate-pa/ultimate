/*
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.ACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.AcslTypeUtils;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CastExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.OldValueExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Translate Boogie expressions to ACSL
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public final class Boogie2ACSL {
	private final TypeSizes mTypeSizes;
	private final CACSL2BoogieBacktranslatorMapping mMapping;
	private final FlatSymbolTable mSymbolTable;
	private final Consumer<String> mReporter;

	public Boogie2ACSL(final TypeSizes typeSizes, final CACSL2BoogieBacktranslatorMapping mapping,
			final FlatSymbolTable symbolTable, final Consumer<String> reporter) {
		mTypeSizes = typeSizes;
		mMapping = mapping;
		mSymbolTable = symbolTable;
		mReporter = reporter;
	}

	public BacktranslatedExpression translateExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.Expression expression, final ILocation context) {
		return translateExpression(expression, context, false);
	}

	private BacktranslatedExpression translateExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.Expression expression, final ILocation context,
			final boolean isNegated) {
		final ILocation loc = expression.getLocation();
		if (loc instanceof ACSLLocation) {
			mReporter.accept("Expression " + BoogiePrettyPrinter.print(expression)
					+ " has an ACSLNode, but we do not support it yet");
			return null;
		}

		if (loc instanceof CLocation) {
			final CLocation cloc = (CLocation) loc;
			if (cloc.ignoreDuringBacktranslation()) {
				// this should lead to nothing
				return null;
			}
		}

		if (expression instanceof de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression) {
			return translateUnaryExpression((de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression) expression,
					context, isNegated);
		}
		if (expression instanceof de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression) {
			return translateBinaryExpression(
					(de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression) expression, context, isNegated);
		}
		if (expression instanceof de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression) {
			return translateIdentifierExpression(
					(de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression) expression, context);
		}
		if (expression instanceof de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral) {
			return translateIntegerLiteral(new BigInteger(
					((de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral) expression).getValue()));
		}
		if (expression instanceof de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral) {
			return translateBooleanLiteral((de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral) expression);
		}
		if (expression instanceof de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral) {
			return translateRealLiteral((de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral) expression);
		}
		if (expression instanceof BitvecLiteral) {
			return translateBitvecLiteral((BitvecLiteral) expression);
		}
		if (expression instanceof de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication) {
			return translateFunctionApplication(
					(de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication) expression, context,
					isNegated);
		}
		mReporter.accept(
				"Expression type not yet supported in backtranslation: " + expression.getClass().getSimpleName());
		return null;
	}

	private BacktranslatedExpression translateIdentifierExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression expr, final ILocation context) {
		final String boogieId = expr.getIdentifier();
		if (boogieId.equals(SFO.RES)) {
			// TODO: Can we somehow get the return type here?
			return new BacktranslatedExpression(new ACSLResultExpression());
		} else if (mMapping.hasVar(boogieId, expr.getDeclarationInformation())) {
			final Pair<String, CType> pair = mMapping.getVar(boogieId, expr.getDeclarationInformation());
			if (isPresentInContext(pair.getFirst(), context)) {
				final var range = getRangeForCType(pair.getSecond());
				return new BacktranslatedExpression(new IdentifierExpression(pair.getFirst()), pair.getSecond(),
						range.getFirst(), range.getSecond());
			}
		} else if (mMapping.hasInVar(boogieId, expr.getDeclarationInformation())) {
			// invars can only occur in expressions as part of synthetic expressions, and then they represent oldvars
			final Pair<String, CType> pair = mMapping.getInVar(boogieId, expr.getDeclarationInformation());
			final var range = getRangeForCType(pair.getSecond());
			return new BacktranslatedExpression(new OldValueExpression(new IdentifierExpression(pair.getFirst())),
					pair.getSecond(), range.getFirst(), range.getSecond());
		}
		return null;
	}

	private static BacktranslatedExpression constructFloat(final BitvecLiteral sign, final BitvecLiteral exponent,
			final BitvecLiteral fraction) {
		// TODO: Should we rather represent this C-float using scientific notation (e.g. -1.57E13)?
		final String bit = bitvecToString(sign) + bitvecToString(exponent) + bitvecToString(fraction);
		final BigDecimal f = getDecimalFromBinaryString(bit);
		return new BacktranslatedExpression(new RealLiteral(f.toPlainString()));
	}

	private static BigDecimal getDecimalFromBinaryString(final String binary) {
		final int len = binary.length();
		if (len == 32) {
			final int intBits = Integer.parseUnsignedInt(binary, 2);
			final float floatValue = Float.intBitsToFloat(intBits);
			return BigDecimal.valueOf(floatValue);
		} else if (len == 64) {
			final long longBits = Long.parseUnsignedLong(binary, 2);
			final double doubleValue = Double.longBitsToDouble(longBits);
			return BigDecimal.valueOf(doubleValue);
		} else {
			throw new IllegalArgumentException("Unsupported length: " + len);
		}
	}

	private static String bitvecToString(final BitvecLiteral lit) {
		final String binStr = new BigInteger(lit.getValue()).toString(2);
		assert binStr.length() <= lit.getLength() : "Binary string cannot be longer than bitvector literal length";
		final int missingZeros = lit.getLength() - binStr.length();
		if (missingZeros > 0) {
			final String formatStr = "%" + lit.getLength() + "s";
			return String.format(formatStr, binStr).replace(' ', '0');
		}
		return binStr;
	}

	// TODO: Currently we don't care about types here, since function applications should only occur in bitvector
	// setting, where we should not need any casts.
	private BacktranslatedExpression translateFunctionApplication(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication fun, final ILocation context,
			final boolean isNegated) {
		final BacktranslatedExpression[] translatedArguments = new BacktranslatedExpression[fun.getArguments().length];
		for (int i = 0; i < fun.getArguments().length; i++) {
			translatedArguments[i] = translateExpression(fun.getArguments()[i], context, isNegated);
			if (translatedArguments[i] == null) {
				return null;
			}
		}
		final String function = fun.getIdentifier();
		final Pair<String, Integer> reversed = SFO.reverseBoogieFunctionName(function);
		if (reversed == null) {
			mReporter.accept("Cannot identify Boogie2SMT function " + function);
			return null;
		}
		final Integer bitSize = reversed.getSecond();

		switch (reversed.getFirst()) {
		case "sign_extend":
		case "zero_extend":
			// TODO: This might be problematic for signed types!
			return translatedArguments[0];
		case "fp":
			if (Arrays.stream(fun.getArguments()).allMatch(BitvecLiteral.class::isInstance)) {
				// this function is used to construct floating points
				return constructFloat((BitvecLiteral) fun.getArguments()[0], (BitvecLiteral) fun.getArguments()[1],
						(BitvecLiteral) fun.getArguments()[2]);
			}
			mReporter.accept("fp can only be backtranslated, if the arguments are literals: " + fun);
			return null;
		case "NaN":
			return new BacktranslatedExpression(new RealLiteral(String.valueOf(Float.NaN)));
		case "bvadd":
			final Expression addition = new BinaryExpression(Operator.ARITHPLUS, translatedArguments[0].getExpression(),
					translatedArguments[1].getExpression());
			return new BacktranslatedExpression(new BinaryExpression(Operator.ARITHMOD, addition,
					new IntegerLiteral(String.valueOf(1L << bitSize))));
		case "bvmul":
			return new BacktranslatedExpression(new BinaryExpression(Operator.ARITHMUL,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvsub":
			final Expression sub = new BinaryExpression(Operator.ARITHMINUS, translatedArguments[0].getExpression(),
					translatedArguments[1].getExpression());
			return new BacktranslatedExpression(
					new BinaryExpression(Operator.ARITHMOD, sub, new IntegerLiteral(String.valueOf(1L << bitSize))));
		case "bvand":
			return new BacktranslatedExpression(new BinaryExpression(Operator.BITAND,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvor":
			return new BacktranslatedExpression(new BinaryExpression(Operator.BITOR,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvxor":
			return new BacktranslatedExpression(new BinaryExpression(Operator.BITXOR,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvshl":
			return new BacktranslatedExpression(new BinaryExpression(Operator.BITSHIFTLEFT,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvashr":
			return new BacktranslatedExpression(new BinaryExpression(Operator.BITSHIFTRIGHT,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvslt":
		case "bvult":
			return new BacktranslatedExpression(new BinaryExpression(Operator.COMPLT,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvsle":
		case "bvule":
			return new BacktranslatedExpression(new BinaryExpression(Operator.COMPLEQ,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvsgt":
		case "bvugt":
			return new BacktranslatedExpression(new BinaryExpression(Operator.COMPGT,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvsge":
		case "bvuge":
			return new BacktranslatedExpression(new BinaryExpression(Operator.COMPGEQ,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvsdiv":
		case "bvudiv":
			return new BacktranslatedExpression(new BinaryExpression(Operator.ARITHDIV,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvsrem":
		case "bvurem":
			return new BacktranslatedExpression(new BinaryExpression(Operator.ARITHMOD,
					translatedArguments[0].getExpression(), translatedArguments[1].getExpression()));
		case "bvneg":
			return new BacktranslatedExpression(
					new UnaryExpression(UnaryExpression.Operator.MINUS, translatedArguments[0].getExpression()));
		case "bvnot":
			return new BacktranslatedExpression(new UnaryExpression(UnaryExpression.Operator.LOGICCOMPLEMENT,
					translatedArguments[0].getExpression()));
		default:
			mReporter.accept("Missing case for function " + function);
			return null;
		}
	}

	private BacktranslatedExpression translateBitvecLiteral(final BitvecLiteral lit) {
		BigInteger value = new BigInteger(lit.getValue());
		// this is only the isSigned case
		final BigInteger maxRepresentablePositiveValuePlusOne = BigInteger.TWO.pow(lit.getLength() - 1);
		if (value.compareTo(maxRepresentablePositiveValuePlusOne) >= 0) {
			final BigInteger numberOfValues = BigInteger.TWO.pow(lit.getLength());
			value = value.subtract(numberOfValues);
		}
		return translateIntegerLiteral(value);
	}

	private static BacktranslatedExpression
			translateRealLiteral(final de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral expression) {
		// TODO: Can we determine the CType here?
		return new BacktranslatedExpression(new RealLiteral(expression.getValue()));
	}

	private static BacktranslatedExpression
			translateBooleanLiteral(final de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral lit) {
		final String value = lit.getValue() ? "1" : "0";
		final BigInteger intValue = new BigInteger(value);
		return new BacktranslatedExpression(new IntegerLiteral(value), new CPrimitive(CPrimitives.INT), intValue,
				intValue);
	}

	private BacktranslatedExpression translateIntegerLiteral(final BigInteger value) {
		final String valueString = value.toString();
		final CPrimitive longlong = new CPrimitive(CPrimitives.LONGLONG);
		if (fitsInType(value, longlong)) {
			// If the literal fits into long long, we can just use the Boogie literal with a matching type
			final CPrimitive type = ISOIEC9899TC3.determineTypeForIntegerLiteral(valueString, mTypeSizes);
			return new BacktranslatedExpression(new IntegerLiteral(valueString), type, value, value);
		}
		final CPrimitive ulonglong = new CPrimitive(CPrimitives.ULONGLONG);
		if (fitsInType(value, ulonglong)) {
			// If it still fits into unsigned long long we can just append the unsigned suffix
			return new BacktranslatedExpression(new IntegerLiteral(valueString + "U"), ulonglong, value, value);
		}
		final CPrimitive int128 = new CPrimitive(CPrimitives.INT128);
		final CPrimitive uint128 = new CPrimitive(CPrimitives.UINT128);
		if (!fitsInType(value, int128) && !fitsInType(value, uint128)) {
			throw new UnsupportedOperationException(
					"Unable to backtranslate " + valueString + ", there is no C type to represent it.");
		}
		// Otherwise we need to split the literal x to ((x / 2^N) << N) | (x % 2^N)
		// (where N are the number of bits for long long; using appropriate casts)
		final CPrimitive resultType = value.signum() >= 0 ? uint128 : int128;
		final var split =
				value.abs().divideAndRemainder(mTypeSizes.getMaxValueOfPrimitiveType(ulonglong).add(BigInteger.ONE));
		final Expression upper = new CastExpression(AcslTypeUtils.translateCTypeToAcslType(resultType),
				translateIntegerLiteral(split[0]).getExpression());
		final Expression shift = new IntegerLiteral(String.valueOf(8 * mTypeSizes.getSize(ulonglong.getType())));
		Expression result = new BinaryExpression(Operator.BITSHIFTLEFT, upper, shift);
		if (split[1].signum() != 0) {
			result = new BinaryExpression(Operator.BITOR, result, translateIntegerLiteral(split[1]).getExpression());
		}
		if (value.signum() < 0) {
			result = new UnaryExpression(UnaryExpression.Operator.MINUS, result);
		}
		return new BacktranslatedExpression(result, resultType, value, value);
	}

	private CType determineTypeForArithmeticOperation(final CType type1, final CType type2) {
		if (type1 == null || type2 == null) {
			return null;
		}
		if (!(type1 instanceof CPrimitive) || !(type2 instanceof CPrimitive)) {
			// TODO: What to do here?
			return type1;
		}
		final CPrimitive prim1 = (CPrimitive) type1;
		final CPrimitive prim2 = (CPrimitive) type2;
		if (!prim1.isIntegerType() || !prim2.isIntegerType()) {
			// TODO: What to do here?
			return type1;
		}
		// If the unsigned type has conversion rank greater than or equal to the rank of the signed type, then the
		// operand with the signed type is implicitly converted to the unsigned type.
		if (mTypeSizes.getSize(prim1.getType()) == mTypeSizes.getSize(prim2.getType())) {
			return mTypeSizes.isUnsigned(prim1) ? prim1 : prim2;
		}
		return mTypeSizes.getSize(prim1.getType()) >= mTypeSizes.getSize(prim2.getType()) ? prim1 : prim2;
	}

	private boolean fitsInType(final BigInteger value, final CType type) {
		return fitsInType(value, value, type);
	}

	private boolean fitsInType(final BigInteger minValue, final BigInteger maxValue, final CType type) {
		if (!(type instanceof CPrimitive)) {
			return true;
		}
		final CPrimitive prim = (CPrimitive) type;
		if (!prim.isIntegerType()) {
			return true;
		}
		return (minValue == null || mTypeSizes.getMinValueOfPrimitiveType(prim).compareTo(minValue) <= 0)
				&& (maxValue == null || mTypeSizes.getMaxValueOfPrimitiveType(prim).compareTo(maxValue) >= 0);
	}

	private CType determineTypeForRange(final BigInteger minValue, final BigInteger maxValue) {
		final List<CPrimitives> orderedTypes = List.of(CPrimitives.CHAR, CPrimitives.UCHAR, CPrimitives.SHORT,
				CPrimitives.USHORT, CPrimitives.INT, CPrimitives.UINT, CPrimitives.LONG, CPrimitives.ULONG,
				CPrimitives.LONGLONG, CPrimitives.ULONGLONG, CPrimitives.INT128, CPrimitives.UINT128);
		for (final CPrimitives prim : orderedTypes) {
			final CType type = new CPrimitive(prim);
			if (fitsInType(minValue, maxValue, type)) {
				return type;
			}
		}
		// If we cannot find a matching type, we do not introduce any casts
		return null;
	}

	private BacktranslatedExpression translateBinaryExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression expression, final ILocation context,
			final boolean isNegated) {
		final BacktranslatedExpression lhs = translateExpression(expression.getLeft(), context, isNegated);
		final BacktranslatedExpression rhs = translateExpression(expression.getRight(), context, isNegated);
		final BigInteger leftMinValue = lhs == null ? null : lhs.getMinimalValue();
		final BigInteger leftMaxValue = lhs == null ? null : lhs.getMaximalValue();
		final BigInteger rightMinValue = rhs == null ? null : rhs.getMinimalValue();
		final BigInteger rightMaxValue = rhs == null ? null : rhs.getMaximalValue();
		final CType leftType = lhs == null ? null : lhs.getCType();
		final CType rightType = rhs == null ? null : rhs.getCType();
		final Operator operator;
		final BigInteger minValue;
		final BigInteger maxValue;
		CType resultType;
		switch (expression.getOperator()) {
		case ARITHDIV:
			// TODO: backtranslate from euclidic division properly
			minValue = leftMinValue == null || rightMaxValue == null ? null : leftMinValue.divide(rightMaxValue);
			maxValue = leftMaxValue == null || rightMinValue == null ? null : leftMaxValue.divide(rightMinValue);
			operator = Operator.ARITHDIV;
			resultType = leftType;
			break;
		case ARITHMINUS:
			minValue = leftMinValue == null || rightMaxValue == null ? null : leftMinValue.subtract(rightMaxValue);
			maxValue = leftMaxValue == null || rightMinValue == null ? null : leftMaxValue.subtract(rightMinValue);
			operator = Operator.ARITHMINUS;
			resultType = determineTypeForArithmeticOperation(leftType, rightType);
			break;
		case ARITHMOD:
			// TODO: backtranslate from euclidic division properly
			if (rightMinValue != null && rightMinValue.equals(rightMaxValue) && rightMinValue.signum() > 0) {
				maxValue = rightMinValue.subtract(BigInteger.ONE);
				minValue = leftMinValue != null && leftMinValue.signum() >= 0 ? BigInteger.ZERO : maxValue.negate();
			} else {
				// TODO: I am not quite sure about the minimal/maximal values here, so I just keep them for now
				minValue = leftMinValue;
				maxValue = leftMaxValue;
			}
			operator = Operator.ARITHMOD;
			resultType = leftType;
			break;
		case ARITHMUL:
			if (leftMinValue == null || leftMaxValue == null || rightMinValue == null || rightMaxValue == null) {
				minValue = null;
				maxValue = null;
			} else {
				final List<BigInteger> results =
						List.of(leftMinValue.multiply(rightMinValue), leftMinValue.multiply(rightMaxValue),
								leftMaxValue.multiply(rightMinValue), leftMaxValue.multiply(rightMaxValue));
				minValue = results.stream().min(BigInteger::compareTo).get();
				maxValue = results.stream().max(BigInteger::compareTo).get();
			}
			operator = Operator.ARITHMUL;
			resultType = determineTypeForArithmeticOperation(leftType, rightType);
			break;
		case ARITHPLUS:
			minValue = leftMinValue == null || rightMaxValue == null ? null : leftMinValue.add(rightMaxValue);
			maxValue = leftMaxValue == null || rightMinValue == null ? null : leftMaxValue.add(rightMinValue);
			operator = Operator.ARITHPLUS;
			resultType = determineTypeForArithmeticOperation(leftType, rightType);
			break;
		case COMPEQ:
		case LOGICIFF:
			minValue = BigInteger.ZERO;
			maxValue = BigInteger.ONE;
			operator = Operator.COMPEQ;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case COMPGEQ:
			minValue = BigInteger.ZERO;
			maxValue = BigInteger.ONE;
			operator = Operator.COMPGEQ;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case COMPGT:
			minValue = BigInteger.ZERO;
			maxValue = BigInteger.ONE;
			operator = Operator.COMPGT;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case COMPLEQ:
			minValue = BigInteger.ZERO;
			maxValue = BigInteger.ONE;
			operator = Operator.COMPLEQ;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case COMPLT:
			minValue = BigInteger.ZERO;
			maxValue = BigInteger.ONE;
			operator = Operator.COMPLT;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case COMPNEQ:
			minValue = BigInteger.ZERO;
			maxValue = BigInteger.ONE;
			operator = Operator.COMPNEQ;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case LOGICAND:
			if (!isNegated) {
				if (lhs == null) {
					return rhs;
				}
				if (rhs == null) {
					return lhs;
				}
			}
			minValue = BigInteger.ZERO;
			maxValue = BigInteger.ONE;
			operator = Operator.LOGICAND;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case LOGICIMPLIES:
			if (isNegated && lhs == null) {
				return rhs;
			}
			if (lhs == null || rhs == null) {
				return null;
			}
			// !lhs || rhs
			return new BacktranslatedExpression(
					new BinaryExpression(Operator.LOGICOR, lhs.getExpression(), rhs.getExpression()),
					new CPrimitive(CPrimitives.INT), BigInteger.ZERO, BigInteger.ONE);
		case LOGICOR:
			if (isNegated) {
				if (lhs == null) {
					return rhs;
				}
				if (rhs == null) {
					return lhs;
				}
			}
			minValue = BigInteger.ZERO;
			maxValue = BigInteger.ONE;
			operator = Operator.LOGICOR;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case BITVECCONCAT:
		case COMPPO:
			return null;
		default:
			throw new AssertionError("Unknown operator " + expression.getOperator());
		}
		if (lhs == null || rhs == null) {
			return null;
		}
		Expression resultingLhs = lhs.getExpression();
		if (!fitsInType(minValue, maxValue, resultType)) {
			resultType = determineTypeForRange(minValue, maxValue);
			if (resultType != null) {
				resultingLhs = new CastExpression(AcslTypeUtils.translateCTypeToAcslType(resultType), resultingLhs);
			}
		}
		final Expression resultExpr = new BinaryExpression(operator, resultingLhs, rhs.getExpression());
		return new BacktranslatedExpression(resultExpr, resultType, minValue, maxValue);
	}

	private BacktranslatedExpression translateUnaryExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression expr, final ILocation context,
			final boolean isNegated) {
		final Expression resultExpr;
		final BigInteger minValue;
		final BigInteger maxValue;
		final CType cType;
		switch (expr.getOperator()) {
		case ARITHNEGATIVE: {
			final BacktranslatedExpression innerTrans = translateExpression(expr.getExpr(), context, isNegated);
			if (innerTrans == null) {
				return null;
			}
			minValue = innerTrans.getMaximalValue() == null ? null : innerTrans.getMaximalValue().negate();
			maxValue = innerTrans.getMinimalValue() == null ? null : innerTrans.getMinimalValue().negate();
			resultExpr = new UnaryExpression(UnaryExpression.Operator.MINUS, innerTrans.getExpression());
			cType = innerTrans.getCType();
			break;
		}
		case LOGICNEG: {
			final BacktranslatedExpression innerTrans = translateExpression(expr.getExpr(), context, !isNegated);
			if (innerTrans == null) {
				return null;
			}
			minValue = innerTrans.getMaximalValue() == null ? null : innerTrans.getMaximalValue().negate();
			maxValue = innerTrans.getMinimalValue() == null ? null : innerTrans.getMinimalValue().negate();
			resultExpr = new UnaryExpression(UnaryExpression.Operator.LOGICNEG, innerTrans.getExpression());
			cType = innerTrans.getCType();
			break;
		}
		case OLD: {
			final BacktranslatedExpression innerTrans = translateExpression(expr.getExpr(), context, isNegated);
			if (innerTrans == null) {
				return null;
			}
			minValue = innerTrans.getMinimalValue();
			maxValue = innerTrans.getMaximalValue();
			resultExpr = new OldValueExpression(innerTrans.getExpression());
			cType = innerTrans.getCType();
			break;
		}
		default:
			throw new AssertionError("Unhandled case");
		}
		return new BacktranslatedExpression(resultExpr, cType, minValue, maxValue);
	}

	private boolean isPresentInContext(final String cId, final ILocation context) {
		if (context == null || !(context instanceof CLocation)) {
			return true;
		}
		return mSymbolTable.containsCSymbol(((CLocation) context).getNode(), cId);
	}

	private Pair<BigInteger, BigInteger> getRangeForCType(final CType type) {
		if (type == null || !(type.getUnderlyingType() instanceof CPrimitive)) {
			return new Pair<>(null, null);
		}
		final CPrimitive prim = (CPrimitive) type.getUnderlyingType();
		if (!prim.isIntegerType()) {
			return new Pair<>(null, null);
		}
		return new Pair<>(mTypeSizes.getMinValueOfPrimitiveType(prim), mTypeSizes.getMaxValueOfPrimitiveType(prim));
	}

	public static final class BacktranslatedExpression {
		private final Expression mExpression;
		private final CType mCType;
		private final BigInteger mMinimalValue;
		private final BigInteger mMaximalValue;

		public BacktranslatedExpression(final Expression expression) {
			this(expression, null, null, null);
		}

		public BacktranslatedExpression(final Expression expression, final CType cType, final BigInteger minimalValue,
				final BigInteger maximalValue) {
			mExpression = expression;
			mCType = cType;
			mMinimalValue = minimalValue;
			mMaximalValue = maximalValue;
		}

		public Expression getExpression() {
			return mExpression;
		}

		public CType getCType() {
			return mCType;
		}

		private BigInteger getMinimalValue() {
			return mMinimalValue;
		}

		private BigInteger getMaximalValue() {
			return mMaximalValue;
		}

		@Override
		public String toString() {
			return ACSLPrettyPrinter.print(mExpression);
		}
	}
}
