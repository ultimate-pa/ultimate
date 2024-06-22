/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.interpreter;

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;

/**
 * Executes Boogie code, transforming a given valuation of program variables. The result is either a possible valuation
 * after the execution of the statements, or no valuation (an empty Optional) to indicate the execution might block for
 * the given initial valuation.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <V>
 *            the type of valuations
 */
public class BoogieInterpreter<V extends IValuation<V>> {
	public Optional<V> interpret(final V valuation, final Statement stmt) {
		if (stmt instanceof AssignmentStatement) {
			return interpret(valuation, (AssignmentStatement) stmt);
		}
		if (stmt instanceof AssumeStatement) {
			return interpret(valuation, (AssumeStatement) stmt);
		}
		if (stmt instanceof AtomicStatement) {
			return interpret(valuation, ((AtomicStatement) stmt).getBody());
		}
		if (stmt instanceof IfStatement) {
			return interpret(valuation, (IfStatement) stmt);
		}
		throw new UnsupportedOperationException(
				"Statements of type " + stmt.getClass().getSimpleName() + " not yet supported");
	}

	public Optional<V> interpret(final V valuation, final Statement[] stmts) {
		V current = valuation;
		for (final var stmt : stmts) {
			final var next = interpret(current, stmt);
			if (next.isEmpty()) {
				return next;
			}
			current = next.get();
		}
		return Optional.of(current);
	}

	private Optional<V> interpret(final V valuation, final AssignmentStatement assign) {
		V current = valuation;
		for (int i = 0; i < assign.getLhs().length; ++i) {
			final var lhs = assign.getLhs()[i];
			final var rhs = assign.getRhs()[i];
			if (lhs instanceof VariableLHS) {
				final var variable = ((VariableLHS) lhs).getIdentifier();
				if (isBool(rhs.getType())) {
					current = current.updateBoolean(variable, evaluateBoolean(rhs, valuation));
				} else if (isInteger(rhs.getType())) {
					current = current.updateInteger(variable, evaluateInteger(rhs, valuation));
				} else {
					throw new IllegalArgumentException("Only booleans and integers currently supported");
				}
			} else {
				throw new IllegalArgumentException("Only variable assignments currently supported");
			}
		}
		return Optional.of(current);
	}

	private Optional<V> interpret(final V valuation, final AssumeStatement assume) {
		if (evaluateBoolean(assume.getFormula(), valuation)) {
			return Optional.of(valuation);
		}
		return Optional.empty();
	}

	private Optional<V> interpret(final V valuation, final IfStatement ifThenElse) {
		if (evaluateBoolean(ifThenElse.getCondition(), valuation)) {
			return interpret(valuation, ifThenElse.getThenPart());
		}
		final var elsePart = ifThenElse.getElsePart();
		if (elsePart == null || elsePart.length == 0) {
			return Optional.of(valuation);
		}
		return interpret(valuation, elsePart);
	}

	private static boolean isBool(final IBoogieType type) {
		if (!(type instanceof BoogiePrimitiveType)) {
			return false;
		}
		return ((BoogiePrimitiveType) type).getTypeCode() == BoogiePrimitiveType.BOOL;
	}

	private static boolean isInteger(final IBoogieType type) {
		if (!(type instanceof BoogiePrimitiveType)) {
			return false;
		}
		return ((BoogiePrimitiveType) type).getTypeCode() == BoogiePrimitiveType.INT;
	}

	public boolean evaluateBoolean(final Expression expr, final V valuation) {
		if (expr instanceof BooleanLiteral) {
			return ((BooleanLiteral) expr).getValue();
		}
		if (expr instanceof IdentifierExpression) {
			return valuation.getBoolean(((IdentifierExpression) expr).getIdentifier());
		}
		if (expr instanceof BinaryExpression) {
			return evaluateBooleanBinary((BinaryExpression) expr, valuation);
		}
		if (expr instanceof IfThenElseExpression) {
			final var ite = (IfThenElseExpression) expr;
			if (evaluateBoolean(ite.getCondition(), valuation)) {
				return evaluateBoolean(ite.getThenPart(), valuation);
			}
			return evaluateBoolean(ite.getElsePart(), valuation);
		}
		if (expr instanceof UnaryExpression) {
			final var unary = (UnaryExpression) expr;
			assert unary.getOperator() == Operator.LOGICNEG;
			return !evaluateBoolean(unary.getExpr(), valuation);
		}
		throw new UnsupportedOperationException(
				"Expressions of type " + expr.getClass().getSimpleName() + " not yet supported");
	}

	public int evaluateInteger(final Expression expr, final V valuation) {
		if (expr instanceof IntegerLiteral) {
			return Integer.parseInt(((IntegerLiteral) expr).getValue());
		}
		if (expr instanceof IdentifierExpression) {
			return valuation.getInteger(((IdentifierExpression) expr).getIdentifier());
		}
		if (expr instanceof BinaryExpression) {
			return evaluateIntegerBinary((BinaryExpression) expr, valuation);
		}
		if (expr instanceof IfThenElseExpression) {
			final var ite = (IfThenElseExpression) expr;
			if (evaluateBoolean(ite.getCondition(), valuation)) {
				return evaluateInteger(ite.getThenPart(), valuation);
			}
			return evaluateInteger(ite.getElsePart(), valuation);
		}
		if (expr instanceof UnaryExpression) {
			final var unary = (UnaryExpression) expr;
			assert unary.getOperator() == Operator.ARITHNEGATIVE;
			return -evaluateInteger(unary.getExpr(), valuation);
		}
		throw new UnsupportedOperationException(
				"Expressions of type " + expr.getClass().getSimpleName() + " not yet supported");
	}

	private boolean evaluateBooleanBinary(final BinaryExpression expr, final V valuation) {
		final IBoogieType opType;
		switch (expr.getOperator()) {
		case COMPEQ:
			opType = expr.getLeft().getType();
			if (isBool(opType)) {
				return evaluateBoolean(expr.getLeft(), valuation) == evaluateBoolean(expr.getRight(), valuation);
			}
			if (isInteger(opType)) {
				return evaluateInteger(expr.getLeft(), valuation) == evaluateInteger(expr.getRight(), valuation);
			}
			throw new IllegalArgumentException("Only booleans and integers currently supported");
		case COMPGEQ:
			return evaluateInteger(expr.getLeft(), valuation) >= evaluateInteger(expr.getRight(), valuation);
		case COMPGT:
			return evaluateInteger(expr.getLeft(), valuation) > evaluateInteger(expr.getRight(), valuation);
		case COMPLEQ:
			return evaluateInteger(expr.getLeft(), valuation) <= evaluateInteger(expr.getRight(), valuation);
		case COMPLT:
			return evaluateInteger(expr.getLeft(), valuation) <= evaluateInteger(expr.getRight(), valuation);
		case COMPNEQ:
			opType = expr.getLeft().getType();
			if (isBool(opType)) {
				return evaluateBoolean(expr.getLeft(), valuation) != evaluateBoolean(expr.getRight(), valuation);
			}
			if (isInteger(opType)) {
				return evaluateInteger(expr.getLeft(), valuation) != evaluateInteger(expr.getRight(), valuation);
			}
			throw new IllegalArgumentException("Only booleans and integers currently supported");
		case LOGICAND:
			return evaluateBoolean(expr.getLeft(), valuation) && evaluateBoolean(expr.getRight(), valuation);
		case LOGICIFF:
			return evaluateBoolean(expr.getLeft(), valuation) == evaluateBoolean(expr.getRight(), valuation);
		case LOGICIMPLIES:
			return !evaluateBoolean(expr.getLeft(), valuation) || evaluateBoolean(expr.getRight(), valuation);
		case LOGICOR:
			return evaluateBoolean(expr.getLeft(), valuation) || evaluateBoolean(expr.getRight(), valuation);
		default:
			throw new UnsupportedOperationException(expr.getOperator().toString());
		}
	}

	private int evaluateIntegerBinary(final BinaryExpression expr, final V valuation) {
		final var left = evaluateInteger(expr.getLeft(), valuation);
		final var right = evaluateInteger(expr.getRight(), valuation);
		switch (expr.getOperator()) {
		case ARITHDIV:
			return left / right;
		case ARITHMINUS:
			return left - right;
		case ARITHMUL:
			return left * right;
		case ARITHPLUS:
			return left + right;
		default:
			throw new UnsupportedOperationException(expr.getOperator().toString());
		}
	}
}
