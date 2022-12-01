/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BitvectorConstantOperationResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BvOp;

/**
 * Helps with extracting constant values (integers or booleans) from expressions.
 *
 */
public class ValueExtraction {

	private final FlatSymbolTable mSymbolTable;

	public ValueExtraction(final FlatSymbolTable symbolTable) {
		mSymbolTable = symbolTable;
	}

	/**
	 * Extract an integer value from an expression, if possible.
	 *
	 * @param expr
	 *            The expression to evaluate
	 * @param hook
	 *            An AST node used as hook for accessing symbol table entries
	 * @return the value of the expression, if fixed, or null if no such fixed value could be determined
	 */
	public BigInteger extractIntegerValue(final Expression expr, final IASTNode hook) {
		if (expr instanceof IntegerLiteral) {
			return extractIntegerValueFromIntegerLiteral((IntegerLiteral) expr);
		} else if (expr instanceof BitvecLiteral) {
			final BigInteger result = extractIntegerValueFromBitvectorLiteral((BitvecLiteral) expr);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof IdentifierExpression) {
			final BigInteger result = extractIntegerValueFromIdentifierExpression((IdentifierExpression) expr, hook);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof BinaryExpression) {
			final BigInteger result = extractIntegerValueFromBinaryExpression((BinaryExpression) expr, hook);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof IfThenElseExpression) {
			final BigInteger result = extractIntegerValueFromIfThenElseExpression(expr, hook);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof FunctionApplication) {
			final BigInteger result = extractIntegerValueFromBitvectorFunctionApplication(expr, hook);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof BitVectorAccessExpression) {
			final BigInteger result =
					extractIntegerValueFromBitVectorAccessExpression((BitVectorAccessExpression) expr, hook);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof UnaryExpression) {
			final BigInteger result = extractIntegerValueFromUnaryExpression((UnaryExpression) expr, hook);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof ArrayAccessExpression || expr instanceof StructAccessExpression) {
			// TODO Dominik 20221121: We could support StructAccessExpression if the struct is a StructConstructor
			return null;
		} else {
			// throw an error for expressions that never have the correct type (e.g. ArrayStoreExpression)
			// as well as for yet unknown expressions.
			throw new AssertionError("Don't know how to extract integer from " + expr.getClass().getSimpleName());
		}
	}

	private BigInteger extractIntegerValueFromBitVectorAccessExpression(final BitVectorAccessExpression expr,
			final IASTNode hook) {
		final Expression operand = expr.getBitvec();
		final BigInteger value = extractIntegerValue(operand, hook);
		if (value == null) {
			return null;
		}
		return ExpressionFactory.constructBitvectorAccessExpressionResult(value, expr.getEnd(), expr.getStart());
	}

	private BigInteger extractIntegerValueFromBitvectorFunctionApplication(final Expression expr, final IASTNode hook) {
		final FunctionApplication funApp = (FunctionApplication) expr;
		final Expression[] args = funApp.getArguments();
		// TODO Matthias 20221119 Avoid code duplication in the following two sections
		if (funApp.getIdentifier().startsWith(SFO.AUXILIARY_FUNCTION_PREFIX + BvOp.sign_extend)) {
			// remove the `~sign_extendFrom` it remains a string of the form aTob, where a
			// and b are natural numbers in a decimal representation
			final String range = funApp.getIdentifier().substring(16);
			final String[] res = range.split("To");
			if (res.length != 2) {
				throw new AssertionError();
			}
			final int from = Integer.parseInt(res[0]);
			final int to = Integer.parseInt(res[1]);
			final BigInteger operand = extractIntegerValue(args[0], hook);
			if (operand == null) {
				return null;
			}
			final BitvectorConstant bv = new BitvectorConstant(operand, BigInteger.valueOf(from));
			return BitvectorConstant.sign_extend(bv, BigInteger.valueOf(to - from)).getValue();
		} else if (funApp.getIdentifier().startsWith(SFO.AUXILIARY_FUNCTION_PREFIX + BvOp.zero_extend)) {
			// remove the `~sign_extendFrom` it remains a string of the form aTob, where a
			// and b are natural numbers in a decimal representation
			final String range = funApp.getIdentifier().substring(16);
			final String[] res = range.split("To");
			if (res.length != 2) {
				throw new AssertionError();
			}
			final int from = Integer.parseInt(res[0]);
			final int to = Integer.parseInt(res[1]);
			final BigInteger operand = extractIntegerValue(args[0], hook);
			if (operand == null) {
				return null;
			}
			final BitvectorConstant bv = new BitvectorConstant(operand, BigInteger.valueOf(from));
			return BitvectorConstant.zero_extend(bv, BigInteger.valueOf(to - from)).getValue();
		}

		final BvOp sbo = getBitvectorSmtFunctionNameFromCFunctionName(funApp.getIdentifier());
		if (sbo == null) {
			// not a bitvector function
			return null;
		}
		if (sbo.isBoolean()) {
			throw new AssertionError("Unexpected boolean bitvector op");
		}
		switch (sbo) {
		case sign_extend:
		case zero_extend:
		case extract:
			throw new UnsupportedOperationException(sbo.name() + " not yet supported but can be implemented");
		default:
			final int index = getBitvectorIndexFromCFunctionName(funApp.getIdentifier());
			if (index == -1) {
				return null;
			}
			final BitvectorConstant[] operands = new BitvectorConstant[sbo.getArity()];
			for (int i = 0; i < args.length; ++i) {
				final BigInteger arg = extractIntegerValue(args[i], hook);
				if (arg == null) {
					return null;
				}
				operands[i] = new BitvectorConstant(arg, BigInteger.valueOf(index));
			}
			final BitvectorConstantOperationResult result = BitvectorConstant.apply(sbo, operands);
			if (result.isBoolean()) {
				throw new AssertionError("Need bitvector result");
			}
			return result.getBvResult().getValue();
		}
	}

	private Boolean extractBooleanValueFromBitvectorFunctionApplication(final Expression expr, final IASTNode hook) {
		final FunctionApplication funApp = (FunctionApplication) expr;

		final BvOp sbo = getBitvectorSmtFunctionNameFromCFunctionName(funApp.getIdentifier());
		if (sbo == null) {
			// not a bitvector function
			return null;
		}
		if (!sbo.isBoolean()) {
			throw new AssertionError("Expected boolean bitvector op");
		}
		final int index = getBitvectorIndexFromCFunctionName(funApp.getIdentifier());
		if (index == -1) {
			return null;
		}
		final BitvectorConstant[] operands = new BitvectorConstant[sbo.getArity()];
		final Expression[] args = funApp.getArguments();
		for (int i = 0; i < args.length; ++i) {
			final BigInteger arg = extractIntegerValue(args[i], hook);
			if (arg == null) {
				return null;
			}
			operands[i] = new BitvectorConstant(arg, BigInteger.valueOf(index));
		}
		final BitvectorConstantOperationResult result = BitvectorConstant.apply(sbo, operands);
		if (!result.isBoolean()) {
			throw new AssertionError("Need Boolean result");
		}
		return result.getBooleanResult();

	}

	private static BigInteger extractIntegerValueFromIntegerLiteral(final IntegerLiteral expr) {
		return new BigInteger(expr.getValue());
	}

	private BigInteger extractIntegerValueFromIfThenElseExpression(final Expression expr, final IASTNode hook) {
		final IfThenElseExpression ifThenElseExpr = (IfThenElseExpression) expr;
		final Boolean condValue = extractBooleanValue(ifThenElseExpr.getCondition(), hook);
		if (condValue != null) {
			if (condValue) {
				return extractIntegerValue(ifThenElseExpr.getThenPart(), hook);
			} else {
				return extractIntegerValue(ifThenElseExpr.getElsePart(), hook);
			}
		}
		return null;
	}

	private BigInteger extractIntegerValueFromBinaryExpression(final BinaryExpression expr, final IASTNode hook) {
		final BigInteger leftValue = extractIntegerValue(expr.getLeft(), hook);
		final BigInteger rightValue = extractIntegerValue(expr.getRight(), hook);
		if (leftValue == null || rightValue == null) {
			return null;
		}
		switch (expr.getOperator()) {
		case ARITHDIV:
			// TODO Matthias 20221119: Division in C may differ from division in Java
			return leftValue.divide(rightValue);
		case ARITHMINUS:
			return leftValue.subtract(rightValue);
		case ARITHMOD:
			// TODO Matthias 20221119: Modulo in C differs from division in Java
			return leftValue.mod(rightValue);
		case ARITHMUL:
			return leftValue.multiply(rightValue);
		case ARITHPLUS:
			return leftValue.add(rightValue);
		case BITVECCONCAT:
			throw new UnsupportedOperationException("BITVECCONCAT not yet supported but can be implemented");
		case COMPEQ:
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT:
		case COMPNEQ:
		case COMPPO:
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR:
			throw new AssertionError("Does not have integer return type: " + expr.getOperator());
		default:
			throw new AssertionError("Unknown operator:" + expr.getOperator());
		}
	}

	private BigInteger extractIntegerValueFromUnaryExpression(final UnaryExpression expr, final IASTNode hook) {
		switch (expr.getOperator()) {
		case ARITHNEGATIVE:
			final BigInteger operandValue = extractIntegerValue(expr.getExpr(), hook);
			if (operandValue == null) {
				return null;
			}
			return operandValue.negate();
		case LOGICNEG:
			throw new AssertionError("Does not have integer return type: " + expr.getOperator());
		case OLD:
			return null;
		default:
			throw new AssertionError("Unknown operator:" + expr.getOperator());
		}
	}

	private static BigInteger extractIntegerValueFromBitvectorLiteral(final BitvecLiteral expr) {
		return new BigInteger(expr.getValue());
	}

	private BigInteger extractIntegerValueFromIdentifierExpression(final IdentifierExpression expr,
			final IASTNode hook) {
		// An IdentifierExpression may be an alias for an integer value, this is stored
		// in the symbol table.
		final String bId = expr.getIdentifier();
		final String cId = mSymbolTable.getCIdForBoogieId(bId);
		final SymbolTableValue stv = mSymbolTable.findCSymbol(hook, cId);
		if (stv != null && stv.hasConstantValue()) {
			return extractIntegerValue(stv.getConstantValue(), hook);
		}
		return null;
	}

	/**
	 * Takes an expression and returns its boolean value, if possible. Returns null otherwise.
	 *
	 * @param expr
	 *            The expression to evaluate
	 * @param hook
	 *            An AST node used to lookup symbol table entries
	 * @return
	 */
	public Boolean extractBooleanValue(final Expression expr, final IASTNode hook) {
		if (expr instanceof BooleanLiteral) {
			return extractBooleanValueFromBooleanLiteral(expr);
		} else if (expr instanceof BinaryExpression) {
			final Boolean result = extractBooleanValueFromBinaryExpression((BinaryExpression) expr, hook);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof UnaryExpression) {
			final Boolean result = extractBooleanValueFromUnaryExpression((UnaryExpression) expr, hook);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof FunctionApplication) {
			final Boolean result = extractBooleanValueFromBitvectorFunctionApplication(expr, hook);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof IdentifierExpression) {
			final Boolean result = extractBooleanValueFromIdentifierExpression((IdentifierExpression) expr, hook);
			if (result != null) {
				throw new AssertionError("Value extraction should only succeed for literals");
			}
			return result;
		} else if (expr instanceof ArrayAccessExpression || expr instanceof StructAccessExpression) {
			// TODO Dominik 20221121: We could support StructAccessExpression if the struct is a StructConstructor
			return null;
		} else {
			// throw an error for expressions that never have the correct type (e.g. ArrayStoreExpression)
			// as well as for yet unknown expressions.
			// TODO Dominik 20221121: We could support IfThenElseExpression, perhaps QuantifierExpression
			throw new AssertionError("Don't know how to extract boolean from " + expr.getClass().getSimpleName());
		}
	}

	private Boolean extractBooleanValueFromIdentifierExpression(final IdentifierExpression expr, final IASTNode hook) {
		// An IdentifierExpression may be an alias for a boolean value, this is stored in the symbol table.
		final String bId = expr.getIdentifier();
		final String cId = mSymbolTable.getCIdForBoogieId(bId);
		final SymbolTableValue stv = mSymbolTable.findCSymbol(hook, cId);
		if (stv != null && stv.hasConstantValue()) {
			return extractBooleanValue(stv.getConstantValue(), hook);
		}
		return null;
	}

	private Boolean extractBooleanValueFromUnaryExpression(final UnaryExpression expr, final IASTNode hook) {
		switch (expr.getOperator()) {
		case LOGICNEG:
			final Boolean operandValue = extractBooleanValue(expr.getExpr(), hook);
			if (operandValue == Boolean.TRUE) {
				return Boolean.FALSE;
			}
			if (operandValue == Boolean.FALSE) {
				return Boolean.TRUE;
			}
			break;
		case OLD:
			return null;
		case ARITHNEGATIVE:
			throw new AssertionError("Not a operation with Boolean return type");
		}
		return null;
	}

	private Boolean extractBooleanValueFromBinaryExpression(final BinaryExpression expr, final IASTNode hook) {
		switch (expr.getOperator()) {
		case ARITHDIV:
		case ARITHMINUS:
		case ARITHMOD:
		case ARITHMUL:
		case ARITHPLUS:
		case BITVECCONCAT:
			throw new AssertionError("Not a operation with Boolean return type");
		case COMPEQ:
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT:
		case COMPNEQ: {
			final BigInteger leftValue = extractIntegerValue(expr.getLeft(), hook);
			final BigInteger rightValue = extractIntegerValue(expr.getRight(), hook);
			if (leftValue == null || rightValue == null) {
				return null;
			}
			switch (expr.getOperator()) {
			case COMPEQ:
				return leftValue.compareTo(rightValue) == 0;
			case COMPNEQ:
				return leftValue.compareTo(rightValue) != 0;
			case COMPLT:
				return leftValue.compareTo(rightValue) < 0;
			case COMPGT:
				return leftValue.compareTo(rightValue) > 0;
			case COMPLEQ:
				return leftValue.compareTo(rightValue) <= 0;
			case COMPGEQ:
				return leftValue.compareTo(rightValue) >= 0;
			default:
				throw new AssertionError();
			}
		}
		case COMPPO:
			throw new AssertionError("We do not use COMPPO in our C translation");
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR: {
			final Boolean leftValue = extractBooleanValue(expr.getLeft(), hook);
			final Boolean rightValue = extractBooleanValue(expr.getRight(), hook);
			if (leftValue == null || rightValue == null) {
				return null;
			}
			switch (expr.getOperator()) {
			case LOGICAND:
				return leftValue && rightValue;
			case LOGICIFF:
				return leftValue.equals(rightValue);
			case LOGICIMPLIES:
				return !leftValue || rightValue;
			case LOGICOR:
				return leftValue || rightValue;
			default:
				throw new AssertionError();
			}

		}
		default:
			throw new AssertionError("Unknown operator:" + expr.getOperator());
		}

	}

	private static Boolean extractBooleanValueFromBooleanLiteral(final Expression expr) {
		return Boolean.valueOf((((BooleanLiteral) expr).getValue()));
	}

	private static BvOp getBitvectorSmtFunctionNameFromCFunctionName(final String name) {
		final String funName = name.substring(1).replaceAll("\\d+", "");
		try {
			return BitvectorConstant.BvOp.valueOf(funName);
		} catch (final IllegalArgumentException iae) {
			return null;
		}
	}

	private static int getBitvectorIndexFromCFunctionName(final String name) {
		try {
			return Integer.parseInt(name.substring(1).replaceAll("[^0-9]", ""));
		} catch (final NumberFormatException ex) {
			return -1;
		}
	}
}
