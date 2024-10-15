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
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.AcslTypeUtils;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CastExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.OldValueExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BigInterval;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

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

	/**
	 * Provides a specialized translation for the 'ensures' clause in a procedure contract. Specifically, it adds
	 * conjuncts of the form 'x == \old(x)' for all global variables that are not modifiable by the procedure, and that
	 * are off-heap (because we assume conservatively that the procedure may modify the heap).
	 *
	 * @param expression
	 *            The original 'ensures' clause to translate
	 * @param context
	 *            The context, i.e., the location of the C function definition
	 * @param modifiableGlobals
	 *            The set of variables listed in the Boogie procedure "modifies" clause
	 * @return A backtranslated ensures clause with the additional conjuncts
	 */
	public BacktranslatedExpression translateEnsuresExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.Expression expression, final ILocation context,
			final Set<de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression> modifiableGlobals) {
		final var intType = new CPrimitive(CPrimitives.INT);
		final var boolRange = BigInterval.booleanRange();

		if (expression == null) {
			return computeOldVarEqualities(modifiableGlobals)
					.map(e -> new BacktranslatedExpression(e, intType, boolRange)).orElse(null);
		}

		final var mainExpression = translateExpression(expression, context);
		final var oldVarEqualities = computeOldVarEqualities(modifiableGlobals);
		if (oldVarEqualities.isPresent()) {
			return new BacktranslatedExpression(
					new BinaryExpression(Operator.LOGICAND, mainExpression.getExpression(), oldVarEqualities.get()),
					new CPrimitive(CPrimitives.INT), BigInterval.booleanRange());
		}

		return mainExpression;
	}

	private Optional<Expression> computeOldVarEqualities(
			final Set<de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression> modifiableGlobals) {
		final var modifiableNames = modifiableGlobals.stream().map(e -> e.getIdentifier()).collect(Collectors.toSet());

		return mSymbolTable.getGlobalScope().entrySet().stream()
				.flatMap(e -> makeOldVarEquality(e.getKey(), e.getValue(), modifiableNames).stream())
				.reduce((eq1, eq2) -> new BinaryExpression(Operator.LOGICAND, eq1, eq2));
	}

	private Optional<Expression> makeOldVarEquality(final String cId, final SymbolTableValue stv,
			final Set<String> modifiableNames) {
		final boolean isTypeDecl = stv.getBoogieDecl() instanceof TypeDeclaration;
		if (isTypeDecl) {
			// Type declarations are not global variables
			return Optional.empty();
		}

		final var boogieName = stv.getBoogieName();
		if (modifiableNames.contains(boogieName)) {
			// No equalities for modifiable variables.
			return Optional.empty();
		}

		if (!mMapping.hasVar(boogieName, stv.getDeclarationInformation())) {
			// We omit the conjunct if the variable cannot be backtranslated and output a warning (sound but imprecise).
			mReporter.accept("Unknown variable: " + boogieName);
			return Optional.empty();
		}

		final var info = mMapping.getVar(boogieName, stv.getDeclarationInformation());
		final boolean isOnHeap = info.getThird();
		if (isOnHeap) {
			// We cannot say whether an on-heap variable is modified, so we omit the conjunct (sound but imprecise).
			//
			// TODO We could check if the procedure can modify the heap. To do so, we would need the Boogie names of the
			// heap data arrays.
			mReporter.accept("Cannot encode non-modifiability of on-heap variable " + cId);
			return Optional.empty();
		}

		final var id = new IdentifierExpression(cId);
		return Optional.of(new BinaryExpression(Operator.COMPEQ, id, new OldValueExpression(id)));
	}

	private BacktranslatedExpression translateExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.Expression expression, final ILocation context,
			final boolean isNegated) {
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
		if (expression instanceof de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression) {
			return translateArrayAccess(
					(de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression) expression, context);
		}
		mReporter.accept(
				"Expression type not yet supported in backtranslation: " + expression.getClass().getSimpleName());
		return null;
	}

	private BacktranslatedExpression translateIdentifierExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression expr, final ILocation context) {
		final String boogieId = expr.getIdentifier();
		if (boogieId.equals(SFO.RES)) {
			final CType type = mMapping.getReturnTypeOfFunction(expr.getDeclarationInformation().getProcedure());
			final var range = getRangeForCType(type);
			return new BacktranslatedExpression(new ACSLResultExpression(), type, range);
		} else if (mMapping.hasVar(boogieId, expr.getDeclarationInformation())) {
			final Triple<String, CType, Boolean> pair = mMapping.getVar(boogieId, expr.getDeclarationInformation());
			// TODO Should we do something different if the variable is on-heap?

			if (isPresentInContext(pair.getFirst(), context)) {
				final var range = getRangeForCType(pair.getSecond());
				return new BacktranslatedExpression(new IdentifierExpression(pair.getFirst()), pair.getSecond(), range);
			}
		} else if (mMapping.hasInVar(boogieId, expr.getDeclarationInformation())) {
			final Pair<String, CType> pair = mMapping.getInVar(boogieId, expr.getDeclarationInformation());
			final var range = getRangeForCType(pair.getSecond());

			if (context instanceof CLocation && ((CLocation) context).getNode() instanceof IASTFunctionDefinition) {
				// In the context of a function definition, i.e., when backtranslating a contract, we can backtranslate
				// invars directly.
				return new BacktranslatedExpression(new IdentifierExpression(pair.getFirst()), pair.getSecond(), range);
			}

			// In all other contexts, in particular for invariants inside a function body, we use \old() to indicate
			// that we are referring to the original value of the parameter in C (because params can be re-assigned).
			return new BacktranslatedExpression(new OldValueExpression(new IdentifierExpression(pair.getFirst())),
					pair.getSecond(), range);
		}
		mReporter.accept("Unknown variable: " + expr.getIdentifier());
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
		return new BacktranslatedExpression(new IntegerLiteral(value), new CPrimitive(CPrimitives.INT),
				BigInterval.singleton(intValue));
	}

	private BacktranslatedExpression translateIntegerLiteral(final BigInteger value) {
		final String valueString = value.toString();
		final CPrimitive longlong = new CPrimitive(CPrimitives.LONGLONG);
		if (fitsInType(value, longlong)) {
			// If the literal fits into long long, we can just use the Boogie literal with a matching type
			final CPrimitive type = ISOIEC9899TC3.determineTypeForIntegerLiteral(valueString, mTypeSizes);
			return new BacktranslatedExpression(new IntegerLiteral(valueString), type, BigInterval.singleton(value));
		}
		final CPrimitive ulonglong = new CPrimitive(CPrimitives.ULONGLONG);
		if (fitsInType(value, ulonglong)) {
			// If it still fits into unsigned long long we can just append the unsigned suffix
			return new BacktranslatedExpression(new IntegerLiteral(valueString + "U"), ulonglong,
					BigInterval.singleton(value));
		}
		final CPrimitive int128 = new CPrimitive(CPrimitives.INT128);
		final CPrimitive uint128 = new CPrimitive(CPrimitives.UINT128);
		if (!fitsInType(value, int128) && !fitsInType(value, uint128)) {
			mReporter.accept("Unable to backtranslate " + valueString + ", there is no C type to represent it.");
			return null;
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
		return new BacktranslatedExpression(result, resultType, BigInterval.singleton(value));
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
		return fitsInType(BigInterval.singleton(value), type);
	}

	private boolean fitsInType(final BigInterval range, final CType type) {
		return getRangeForCType(type).contains(range);
	}

	private CType determineTypeForRange(final BigInterval range) {
		final List<CPrimitives> orderedTypes = List.of(CPrimitives.CHAR, CPrimitives.UCHAR, CPrimitives.SHORT,
				CPrimitives.USHORT, CPrimitives.INT, CPrimitives.UINT, CPrimitives.LONG, CPrimitives.ULONG,
				CPrimitives.LONGLONG, CPrimitives.ULONGLONG, CPrimitives.INT128, CPrimitives.UINT128);
		for (final CPrimitives prim : orderedTypes) {
			final CType type = new CPrimitive(prim);
			if (fitsInType(range, type)) {
				return type;
			}
		}
		// If we cannot find a matching type, we do not introduce any casts
		return null;
	}

	private BacktranslatedExpression translateDiv(final BacktranslatedExpression lhs,
			final BacktranslatedExpression rhs) {
		if (lhs == null || rhs == null) {
			return null;
		}
		final BigInterval leftRange = lhs.getRange();
		final BigInterval rightRange = rhs.getRange();
		final BigInterval resultRange = leftRange.euclideanDivide(rightRange);
		final Expression baseExpr = new BinaryExpression(Operator.ARITHDIV, lhs.getExpression(), rhs.getExpression());
		if (leftRange.isStrictlyNonNegative()) {
			if (resultRange.isSingleton()) {
				return translateIntegerLiteral(resultRange.getMinValue());
			}
			return new BacktranslatedExpression(baseExpr, lhs.getCType(), resultRange);
		}
		// If the left operand might be negative, we need to translate euclidian modulo to remainder
		// (they only coincide, if the left operand is positive)
		final Expression posExpr = new BinaryExpression(Operator.ARITHMINUS,
				new BinaryExpression(Operator.ARITHDIV, lhs.getExpression(), rhs.getExpression()),
				new IntegerLiteral("1"));
		final Expression negExpr = new BinaryExpression(Operator.ARITHPLUS,
				new BinaryExpression(Operator.ARITHDIV, lhs.getExpression(), rhs.getExpression()),
				new IntegerLiteral("1"));
		final Expression expr;
		if (rightRange.isStrictlyNonNegative()) {
			expr = posExpr;
		} else if (rightRange.isStrictlyNonPositive()) {
			expr = negExpr;
		} else {
			expr = new IfThenElseExpression(
					new BinaryExpression(Operator.COMPGEQ, rhs.getExpression(), new IntegerLiteral("0")), posExpr,
					negExpr);
		}
		if (leftRange.isStrictlyNonPositive()) {
			return new BacktranslatedExpression(expr, lhs.getCType(), resultRange);
		}
		return new BacktranslatedExpression(new IfThenElseExpression(
				new BinaryExpression(Operator.COMPGEQ, lhs.getExpression(), new IntegerLiteral("0")), baseExpr, expr),
				lhs.getCType(), resultRange);
	}

	private BacktranslatedExpression translateModulo(final BacktranslatedExpression lhs,
			final BacktranslatedExpression rhs) {
		if (lhs == null || rhs == null) {
			return null;
		}
		final BigInterval leftRange = lhs.getRange();
		final BigInterval rightRange = rhs.getRange();
		if (rightRange.isStrictlyPositive()) {
			final var minModRange = new BigInterval(BigInteger.ZERO, rightRange.getMinValue().subtract(BigInteger.ONE));
			if (minModRange.contains(leftRange)) {
				// Avoid unnecessary modulo, it does not have any effect (since the lhs is already "in range")
				return lhs;
			}
		}
		final Expression baseExpr = new BinaryExpression(Operator.ARITHMOD, lhs.getExpression(), rhs.getExpression());
		final BigInterval resultRange = leftRange.euclideanModulo(rightRange);
		if (leftRange.isStrictlyNonNegative()) {
			return new BacktranslatedExpression(baseExpr, lhs.getCType(), resultRange);
		}
		// If the left operand might be negative, we need to translate euclidian modulo to remainder
		// (they only coincide, if the left operand is positive)
		final Expression posExpr = new BinaryExpression(Operator.ARITHPLUS,
				new BinaryExpression(Operator.ARITHMOD, lhs.getExpression(), rhs.getExpression()), rhs.getExpression());
		final Expression negExpr = new BinaryExpression(Operator.ARITHMINUS,
				new BinaryExpression(Operator.ARITHMOD, lhs.getExpression(), rhs.getExpression()), rhs.getExpression());
		final Expression expr;
		if (rightRange.isStrictlyNonNegative()) {
			expr = posExpr;
		} else if (rightRange.isStrictlyNonPositive()) {
			expr = negExpr;
		} else {
			expr = new IfThenElseExpression(
					new BinaryExpression(Operator.COMPGEQ, rhs.getExpression(), new IntegerLiteral("0")), posExpr,
					negExpr);
		}
		if (leftRange.isStrictlyNonPositive()) {
			return new BacktranslatedExpression(expr, lhs.getCType(), resultRange);
		}
		return new BacktranslatedExpression(new IfThenElseExpression(
				new BinaryExpression(Operator.COMPGEQ, lhs.getExpression(), new IntegerLiteral("0")), baseExpr, expr),
				lhs.getCType(), resultRange);
	}

	private BacktranslatedExpression translateBinaryExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression expression, final ILocation context,
			final boolean isNegated) {
		final BacktranslatedExpression lhs = translateExpression(expression.getLeft(), context, isNegated);
		final BacktranslatedExpression rhs = translateExpression(expression.getRight(), context, isNegated);
		final BigInterval leftRange = lhs == null ? BigInterval.unbounded() : lhs.getRange();
		final BigInterval rightRange = rhs == null ? BigInterval.unbounded() : rhs.getRange();
		final CType leftType = lhs == null ? null : lhs.getCType();
		final CType rightType = rhs == null ? null : rhs.getCType();
		final Operator operator;
		final BigInterval range;
		CType resultType;
		switch (expression.getOperator()) {
		case ARITHDIV:
			return translateDiv(lhs, rhs);
		case ARITHMINUS:
			if (rightRange.isZero()) {
				return lhs;
			}
			resultType = determineTypeForArithmeticOperation(leftType, rightType);
			range = leftRange.subtract(rightRange);
			operator = Operator.ARITHMINUS;
			break;
		case ARITHMOD:
			return translateModulo(lhs, rhs);
		case ARITHMUL:
			resultType = determineTypeForArithmeticOperation(leftType, rightType);
			range = leftRange.multiply(rightRange);
			operator = Operator.ARITHMUL;
			break;
		case ARITHPLUS:
			if (leftRange.isZero()) {
				return rhs;
			}
			if (rightRange.isZero()) {
				return lhs;
			}
			resultType = determineTypeForArithmeticOperation(leftType, rightType);
			range = leftRange.add(rightRange);
			operator = Operator.ARITHPLUS;
			break;
		case COMPEQ:
			range = BigInterval.booleanRange();
			operator = Operator.COMPEQ;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case COMPGEQ:
			range = BigInterval.booleanRange();
			operator = Operator.COMPGEQ;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case COMPGT:
			range = BigInterval.booleanRange();
			operator = Operator.COMPGT;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case COMPLEQ:
			range = BigInterval.booleanRange();
			operator = Operator.COMPLEQ;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case COMPLT:
			range = BigInterval.booleanRange();
			operator = Operator.COMPLT;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case COMPNEQ:
			range = BigInterval.booleanRange();
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
			range = BigInterval.booleanRange();
			operator = Operator.LOGICAND;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		case LOGICOR:
			if (isNegated) {
				if (lhs == null) {
					return rhs;
				}
				if (rhs == null) {
					return lhs;
				}
			}
			range = BigInterval.booleanRange();
			operator = Operator.LOGICOR;
			resultType = new CPrimitive(CPrimitives.INT);
			break;
		default:
			mReporter.accept("Operator not supported: " + expression.getOperator());
			return null;
		}
		if (lhs == null || rhs == null) {
			return null;
		}
		if (range.isSingleton()) {
			return translateIntegerLiteral(range.getMinValue());
		}
		Expression resultingLhs = lhs.getExpression();
		if (!fitsInType(range, resultType)) {
			resultType = determineTypeForRange(range);
			if (resultType != null) {
				resultingLhs = new CastExpression(AcslTypeUtils.translateCTypeToAcslType(resultType), resultingLhs);
			}
		}
		final Expression resultExpr = new BinaryExpression(operator, resultingLhs, rhs.getExpression());
		return new BacktranslatedExpression(resultExpr, resultType, range);
	}

	private BacktranslatedExpression translateUnaryExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression expr, final ILocation context,
			final boolean isNegated) {
		final Expression resultExpr;
		final BigInterval range;
		final CType cType;
		switch (expr.getOperator()) {
		case ARITHNEGATIVE: {
			final BacktranslatedExpression innerTrans = translateExpression(expr.getExpr(), context, isNegated);
			if (innerTrans == null) {
				return null;
			}
			range = innerTrans.getRange().negate();
			resultExpr = new UnaryExpression(UnaryExpression.Operator.MINUS, innerTrans.getExpression());
			cType = innerTrans.getCType();
			break;
		}
		case LOGICNEG: {
			final BacktranslatedExpression innerTrans = translateExpression(expr.getExpr(), context, !isNegated);
			if (innerTrans == null) {
				return null;
			}
			range = BigInterval.booleanRange();
			resultExpr = new UnaryExpression(UnaryExpression.Operator.LOGICNEG, innerTrans.getExpression());
			cType = innerTrans.getCType();
			break;
		}
		case OLD: {
			final BacktranslatedExpression innerTrans = translateExpression(expr.getExpr(), context, isNegated);
			if (innerTrans == null) {
				return null;
			}
			range = innerTrans.getRange();
			resultExpr = new OldValueExpression(innerTrans.getExpression());
			cType = innerTrans.getCType();
			break;
		}
		default:
			mReporter.accept("Operator not supported: " + expr.getOperator());
			return null;
		}
		return new BacktranslatedExpression(resultExpr, cType, range);
	}

	private boolean isPresentInContext(final String cId, final ILocation context) {
		if (context instanceof CLocation) {
			return mSymbolTable.containsCSymbol(((CLocation) context).getNode(), cId);
		}
		return true;
	}

	private BigInterval getRangeForCType(final CType type) {
		if (type == null || !(type.getUnderlyingType() instanceof CPrimitive)) {
			return BigInterval.unbounded();
		}
		final CPrimitive prim = (CPrimitive) type.getUnderlyingType();
		if (!prim.isIntegerType()) {
			return BigInterval.unbounded();
		}
		return new BigInterval(mTypeSizes.getMinValueOfPrimitiveType(prim),
				mTypeSizes.getMaxValueOfPrimitiveType(prim));
	}

	private BacktranslatedExpression translateArrayAccess(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression expression,
			final ILocation context) {
		final BacktranslatedExpression array = translateExpression(expression.getArray(), context);
		if (array == null) {
			// TODO: Translate pointer accesses back (i.e. array accesses in the memory array)
			// - Check if the array is the memory array first
			// - Then check if the first and second arguments are matching base and offset
			// TODO: Backtranslate valid accesses properly (\valid of the underlying base)
			mReporter.accept("Cannot backtranslate array access to array " + expression.getArray());
			return null;
		}
		Expression result = array.getExpression();
		CType resultType = array.getCType();
		for (final var index : expression.getIndices()) {
			final BacktranslatedExpression translatedIndex = translateExpression(index, context);
			if (translatedIndex == null) {
				return null;
			}
			result = new ArrayAccessExpression(result, new Expression[] { translatedIndex.getExpression() });
			resultType = ((CArray) resultType).getValueType();
		}
		final var range = getRangeForCType(resultType);
		return new BacktranslatedExpression(result, resultType, range);
	}

	public static final class BacktranslatedExpression {
		private final Expression mExpression;
		private final CType mCType;
		private final BigInterval mRange;

		public BacktranslatedExpression(final Expression expression) {
			this(expression, null, BigInterval.unbounded());
		}

		public BacktranslatedExpression(final Expression expression, final CType cType, final BigInterval range) {
			mExpression = expression;
			mCType = cType;
			mRange = Objects.requireNonNull(range);
		}

		public Expression getExpression() {
			return mExpression;
		}

		public CType getCType() {
			return mCType;
		}

		public BigInterval getRange() {
			return mRange;
		}

		@Override
		public String toString() {
			return ACSLPrettyPrinter.print(mExpression);
		}
	}
}
