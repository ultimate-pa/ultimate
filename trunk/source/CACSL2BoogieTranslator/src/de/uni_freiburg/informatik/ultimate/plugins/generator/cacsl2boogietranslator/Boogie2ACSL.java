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
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.ACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression.Operator;
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
	private final CACSL2BoogieBacktranslatorMapping mMapping;
	private final FlatSymbolTable mSymbolTable;
	private final Consumer<String> mReporter;

	public Boogie2ACSL(final CACSL2BoogieBacktranslatorMapping mapping, final FlatSymbolTable symbolTable,
			final Consumer<String> reporter) {
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
				return new BacktranslatedExpression(new IdentifierExpression(pair.getFirst()));
			}
		} else if (mMapping.hasInVar(boogieId, expr.getDeclarationInformation())) {
			// invars can only occur in expressions as part of synthetic expressions, and then they represent oldvars
			final Pair<String, CType> pair = mMapping.getInVar(boogieId, expr.getDeclarationInformation());
			return new BacktranslatedExpression(new OldValueExpression(new IdentifierExpression(pair.getFirst())));
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
		return new BacktranslatedExpression(new RealLiteral(expression.getValue()));
	}

	private static BacktranslatedExpression
			translateBooleanLiteral(final de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral lit) {
		return new BacktranslatedExpression(new IntegerLiteral(lit.getValue() ? "1" : "0"));
	}

	private BacktranslatedExpression translateIntegerLiteral(final BigInteger value) {
		return new BacktranslatedExpression(new IntegerLiteral(value.toString()));
	}

	private BacktranslatedExpression translateBinaryExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression expression, final ILocation context,
			final boolean isNegated) {
		final BacktranslatedExpression lhs = translateExpression(expression.getLeft(), context, isNegated);
		final BacktranslatedExpression rhs = translateExpression(expression.getRight(), context, isNegated);

		final Operator operator;
		switch (expression.getOperator()) {
		case ARITHDIV:
			// TODO: backtranslate from euclidic division properly
			operator = Operator.ARITHDIV;
			break;
		case ARITHMINUS:
			operator = Operator.ARITHMINUS;
			break;
		case ARITHMOD:
			// TODO: backtranslate from euclidic division properly
			operator = Operator.ARITHMOD;
			break;
		case ARITHMUL:
			operator = Operator.ARITHMUL;
			break;
		case ARITHPLUS:
			operator = Operator.ARITHPLUS;
			break;
		case COMPEQ:
		case LOGICIFF:
			operator = Operator.COMPEQ;
			break;
		case COMPGEQ:
			operator = Operator.COMPGEQ;
			break;
		case COMPGT:
			operator = Operator.COMPGT;
			break;
		case COMPLEQ:
			operator = Operator.COMPLEQ;
			break;
		case COMPLT:
			operator = Operator.COMPLT;
			break;
		case COMPNEQ:
			operator = Operator.COMPNEQ;
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
			operator = Operator.LOGICAND;
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
					new BinaryExpression(Operator.LOGICOR, lhs.getExpression(), rhs.getExpression()));
		case LOGICOR:
			if (isNegated) {
				if (lhs == null) {
					return rhs;
				}
				if (rhs == null) {
					return lhs;
				}
			}
			operator = Operator.LOGICOR;
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
		return new BacktranslatedExpression(new BinaryExpression(operator, lhs.getExpression(), rhs.getExpression()));
	}

	private BacktranslatedExpression translateUnaryExpression(
			final de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression expr, final ILocation context,
			final boolean isNegated) {
		final Expression resultExpr;
		switch (expr.getOperator()) {
		case ARITHNEGATIVE: {
			final BacktranslatedExpression innerTrans = translateExpression(expr.getExpr(), context, isNegated);
			if (innerTrans == null) {
				return null;
			}
			resultExpr = new UnaryExpression(UnaryExpression.Operator.MINUS, innerTrans.getExpression());
			break;
		}
		case LOGICNEG: {
			final BacktranslatedExpression innerTrans = translateExpression(expr.getExpr(), context, !isNegated);
			if (innerTrans == null) {
				return null;
			}
			resultExpr = new UnaryExpression(UnaryExpression.Operator.LOGICNEG, innerTrans.getExpression());
			break;
		}
		case OLD: {
			final BacktranslatedExpression innerTrans = translateExpression(expr.getExpr(), context, isNegated);
			if (innerTrans == null) {
				return null;
			}
			resultExpr = new OldValueExpression(innerTrans.getExpression());
			break;
		}
		default:
			throw new AssertionError("Unhandled case");
		}
		return new BacktranslatedExpression(resultExpr);

	}

	private boolean isPresentInContext(final String cId, final ILocation context) {
		if (context == null || !(context instanceof CLocation)) {
			return true;
		}
		return mSymbolTable.containsCSymbol(((CLocation) context).getNode(), cId);
	}

	public static final class BacktranslatedExpression {
		private final Expression mExpression;

		public BacktranslatedExpression(final Expression expression) {
			mExpression = expression;
		}

		public Expression getExpression() {
			return mExpression;
		}

		@Override
		public String toString() {
			return ACSLPrettyPrinter.print(mExpression);
		}
	}
}
