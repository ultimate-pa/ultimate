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

package de.uni_freiburg.informatik.ultimate.model.acsl;

import java.util.Arrays;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLAllExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLType;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assertion;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.AtLabelExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BaseAddrExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BlockLengthExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CastExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnotStmt;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Ensures;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FieldAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FreeableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GhostDeclaration;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalGhostDeclaration;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.MallocableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.NotDefinedExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.NullPointer;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.OldValueExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Requires;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.SizeOfExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.SyntacticNamingExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ValidExpression;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ACSLPrettyPrinter {
	private static final String STRING_AND = "&";
	private static final String STRING_MINUS = "-";
	private static final String STRING_TIMES = "*";
	private static final String STRING_PLUS = "+";

	public static String print(final ACSLNode node) {
		switch (node) {
		case final CodeAnnotStmt codeAnnot:
			return print(codeAnnot.getCodeStmt());
		case final Assertion assertion:
			return "//@ assert " + printExpression(assertion.getFormula()) + ";";
		case final Expression expr:
			return printExpression(expr);
		case final GhostDeclaration decl:
			return printGhostDeclaration(decl.getType(), decl.getIdentifier(), decl.getExpr());
		case final GlobalGhostDeclaration decl:
			return printGhostDeclaration(decl.getType(), decl.getIdentifier(), decl.getExpr());
		case final GhostUpdate update:
			return String.format("//@ ghost %s = %s;", update.getIdentifier(), printExpression(update.getExpr()));
		case final LoopInvariant loopInv:
			return "//@ loop invariant " + printExpression(loopInv.getFormula()) + ";";
		case final Requires req:
			return "//@ requires " + printExpression(req.getFormula()) + ";";
		case final Ensures ens:
			return "//@ ensures " + printExpression(ens.getFormula()) + ";";
		default:
			// TODO: Add more cases
			return node.toString();
		}
	}

	private static String printGhostDeclaration(final ACSLType type, final String identifier, final Expression expr) {
		final StringBuilder sb = new StringBuilder();
		sb.append("//@ ghost ").append(type.getTypeName()).append(' ').append(identifier);
		if (expr != null) {
			sb.append(" = ").append(printExpression(expr));
		}
		return sb.append(';').toString();
	}

	private static String printExpression(final Expression expression) {
		return switch (expression) {
		case final ACSLAllExpression all -> "\\all";
		case final ACSLResultExpression res -> "\\result";
		case final ArrayAccessExpression arrayAccess -> "%s[%s]".formatted(
				printExpression(arrayAccess.getArray(), arrayAccess), printExpression(arrayAccess.getIndex()));
		case final AtLabelExpression at -> "\\at(%s, %s)".formatted(printExpression(at.getExpression()), at.getLabel());
		case final BaseAddrExpression base -> "\\base_addr{%s}".formatted(printExpression(base.getExpression()));
		case final BinaryExpression bin -> printBinaryExpression(bin);
		case final BlockLengthExpression block ->
				"\\block_length{%s}".formatted(printExpression(block.getExpression()));
		case final BooleanLiteral boolLit -> "\\" + boolLit.getValue();
		case final CastExpression cast ->
				"(%s) %s".formatted(cast.getCastedType().getTypeName(), printExpression(cast.getExpression(), cast));
		case final FieldAccessExpression f -> "%s.%s".formatted(printExpression(f.getStruct(), f), f.getField());
		case final FreeableExpression freeable -> "\\freeable{%s}".formatted(printExpression(freeable.getExpression()));
		case final FunctionApplication function -> "%s(%s)".formatted(function.getIdentifier(),
				Arrays.stream(function.getArguments()).map(x -> printExpression(x)).collect(Collectors.joining(", ")));
		case final IdentifierExpression id -> id.getIdentifier();
		case final IfThenElseExpression ite -> "%s ? %s : %s".formatted(printExpression(ite.getCondition(), ite),
				printExpression(ite.getThenPart(), ite), printExpression(ite.getElsePart(), ite));
		case final IntegerLiteral intLit -> intLit.getValue();
		case final MallocableExpression malloc -> "\\mallocable{%s}".formatted(printExpression(malloc.getExpression()));
		case final NotDefinedExpression nd ->
				throw new AssertionError("NotDefinedExpression should not be shown as a string, "
						+ "it should be only used for unsupported ACSL expressions.");
		case final NullPointer np -> "\\null";
		case final OldValueExpression old -> "\\old(%s)".formatted(printExpression(old.getExpression()));
		case final QuantifierExpression quantifier -> printQuantifierExpression(quantifier);
		case final RealLiteral realLit -> realLit.getValue();
		case final SizeOfExpression sizeof -> "sizeof(%s)".formatted(printExpression(sizeof.getExpression()));
		case final StringLiteral string -> "\"%s\"".formatted(string.getValue());
		case final SyntacticNamingExpression naming ->
				"%s : %s".formatted(naming.getIdentifier(), printExpression(naming.getExpression(), naming));
		case final UnaryExpression unary -> printUnaryExpression(unary);
		case final ValidExpression valid -> "\\valid(%s)".formatted(printExpression(valid.getExpression()));
		};
	}

	private static String printQuantifierExpression(final QuantifierExpression quantifier) {
		final String quantor = quantifier.isUniversal() ? "\\forall" : "\\exists";
		final String vars = Arrays.stream(quantifier.getVariables())
				.map(x -> x.getType().getTypeName() + " " + x.getName()).collect(Collectors.joining(", "));
		return "%s %s; %s".formatted(quantor, vars, printExpression(quantifier.getSubformula(), quantifier));
	}

	private static String printUnaryExpression(final UnaryExpression expression) {
		return unaryOperatorToString(expression.getOperator()) + printExpression(expression.getExpr(), expression);
	}

	private static String printBinaryExpression(final BinaryExpression expression) {
		final String op = binaryOperatorToString(expression.getOperator());
		final String left =
				printExpression(expression.getLeft(), expression.getOperator(), Associativity.LEFT_ASSOCIATIVE);
		final String right =
				printExpression(expression.getRight(), expression.getOperator(), Associativity.RIGHT_ASSOCIATIVE);

		return String.format("%s %s %s", left, op, right);
	}

	// Prints the expression, and wraps it in parentheses if the parent expression's precedence is lower.
	private static String printExpression(final Expression expression, final Expression parent) {
		final String expr = printExpression(expression);
		final Precedence precedence = getPrecedence(expression);
		final Precedence parentPrecedence = getPrecedence(parent);
		if (precedence.compareTo(parentPrecedence) > 0) {
			return expr;
		}
		return "(" + expr + ")";
	}

	// Prints the expression, and wraps it in parentheses if the parent binary operator's precedence is lower,
	// unless associativity rules permit omitting the parentheses.
	private static String printExpression(final Expression expression, final BinaryExpression.Operator parentOperator,
			final Associativity requiredAssoc) {
		final String expr = printExpression(expression);
		final Precedence precedence = getPrecedence(expression);
		final Precedence parentPrecedence = getPrecedence(parentOperator);

		if (precedence.compareTo(parentPrecedence) > 0) {
			return expr;
		}
		if (expression instanceof final BinaryExpression bExp && bExp.getOperator() == parentOperator
				&& getAssociativity(parentOperator).satisfies(requiredAssoc)) {
			return expr;
		}
		return "(" + expr + ")";
	}

	public static String unaryOperatorToString(final UnaryExpression.Operator operator) {
		return switch (operator) {
		case ADDROF -> STRING_AND;
		case LOGICNEG -> "!";
		case LTLFINALLY -> "F";
		case LTLGLOBALLY -> "G";
		case LTLNEXT -> "X";
		case MINUS -> STRING_MINUS;
		case PLUS -> STRING_PLUS;
		case POINTER -> STRING_TIMES;
		case LOGICCOMPLEMENT -> "~";
		};
	}

	public static String binaryOperatorToString(final BinaryExpression.Operator operator) {
		return switch (operator) {
		case ARITHDIV -> "/";
		case ARITHMINUS -> STRING_MINUS;
		case ARITHMOD -> "%";
		case ARITHMUL -> STRING_TIMES;
		case ARITHPLUS -> STRING_PLUS;
		case BITAND -> STRING_AND;
		case BITIFF -> "<-->";
		case BITIMPLIES -> "-->";
		case BITOR -> "|";
		case BITXOR -> "^";
		case COMPEQ -> "==";
		case COMPGEQ -> ">=";
		case COMPGT -> ">";
		case COMPLEQ -> "<=";
		case COMPLT -> "<";
		case COMPNEQ -> "!=";
		case LOGICAND -> "&&";
		case LOGICIFF -> "<==>";
		case LOGICIMPLIES -> "==>";
		case LOGICOR -> "||";
		case LOGICXOR -> "^^";
		case BITSHIFTLEFT -> "<<";
		case BITSHIFTRIGHT -> ">>";
		case LTLUNTIL -> "U";
		case LTLRELEASE -> "R";
		case LTLWEAKUNTIL -> "WU";
		case COMPPO, BITVECCONCAT -> throw new AssertionError("Unhandled operator " + operator);
		};
	}

	// See Section 2.2.1 of the ACSL standard.
	private static Precedence getPrecedence(final Expression expression) {
		return switch (expression) {
		case final BinaryExpression binExp -> getPrecedence(binExp.getOperator());
		case final CastExpression castExp -> Precedence.UNARY;
		case final FieldAccessExpression faExp -> Precedence.SELECTION;
		case final IfThenElseExpression iteExp -> Precedence.TERNARY;
		case final QuantifierExpression quantExp -> Precedence.BINDING;
		case final UnaryExpression unExp -> Precedence.UNARY;
		case final SyntacticNamingExpression synExp -> Precedence.NAMING;

		// unambiguous / highest precedence
		case final ACSLResultExpression resExp -> Precedence.TOP;
		case final AtLabelExpression atExp -> Precedence.TOP;
		case final BaseAddrExpression baseExp -> Precedence.TOP;
		case final BlockLengthExpression blockExp -> Precedence.TOP;
		case final BooleanLiteral bLit -> Precedence.TOP;
		case final FreeableExpression freeExp -> Precedence.TOP;
		case final FunctionApplication funApp -> Precedence.TOP;
		case final IdentifierExpression idExp -> Precedence.TOP;
		case final IntegerLiteral intLit -> Precedence.TOP;
		case final MallocableExpression malExp -> Precedence.TOP;
		case final NullPointer np -> Precedence.TOP;
		case final OldValueExpression oldExp -> Precedence.TOP;
		case final RealLiteral rLit -> Precedence.TOP;
		case final SizeOfExpression sizeExp -> Precedence.TOP;
		case final StringLiteral strLit -> Precedence.TOP;
		case final ValidExpression valExp -> Precedence.TOP;

		// safe assumption: expression has lowest possible precedence
		default -> Precedence.BOTTOM;
		};
	}

	// See Section 2.2.1 of the ACSL standard.
	// For custom additions (LTL), this follows the precedence defined in our parser (see GlobalLocalParser.cup).
	private static Precedence getPrecedence(final BinaryExpression.Operator operator) {
		return switch (operator) {
		case LOGICIFF -> Precedence.EQUIV;
		case LOGICIMPLIES -> Precedence.IMPLIES;
		case LOGICAND, LOGICXOR, LOGICOR -> Precedence.OR_XOR_AND;
		case BITOR -> Precedence.BIT_OR;
		case BITIFF -> Precedence.BIT_EQUIV;
		case BITIMPLIES -> Precedence.BIT_IMPLIES;
		case BITXOR -> Precedence.BIT_XOR;
		case BITAND -> Precedence.BIT_AND;
		case COMPLT, COMPLEQ, COMPGT, COMPGEQ -> Precedence.COMPARISON;
		case COMPEQ, COMPNEQ -> Precedence.EQUALITY;
		case BITSHIFTLEFT, BITSHIFTRIGHT -> Precedence.SHIFT;
		case ARITHPLUS, ARITHMINUS -> Precedence.ADDITIVE;
		case ARITHMUL, ARITHDIV, ARITHMOD -> Precedence.MULTIPLICATIVE;
		case LTLUNTIL, LTLWEAKUNTIL, LTLRELEASE -> Precedence.LTL_INFIX;

		// safe assumption: expression has lowest possible precedence
		case BITVECCONCAT, COMPPO -> Precedence.BOTTOM;
		};
	}

	// See Section 2.2.1 of the ACSL standard for information on left-/right-associativity.
	// For custom additions (LTL), this follows the associativity defined in our parser (see GlobalLocalParser.cup).
	//
	// Note that for operators that are semantically associative, we use the value ASSOCIATIVE rather than
	// LEFT_ASSOCIATIVE resp. RIGHT_ASSOCIATIVE. This allows us to omit parentheses regardless of how subexpressions are
	// nested (to the left of the operator, to the right, or both).
	private static Associativity getAssociativity(final BinaryExpression.Operator operator) {
		return switch (operator) {
		case LOGICIFF -> Associativity.LEFT_ASSOCIATIVE;
		case LOGICIMPLIES -> Associativity.RIGHT_ASSOCIATIVE;

		case LOGICAND, LOGICOR -> Associativity.ASSOCIATIVE;
		case LOGICXOR -> Associativity.LEFT_ASSOCIATIVE;

		case BITAND, BITOR -> Associativity.ASSOCIATIVE;
		case BITIFF -> Associativity.LEFT_ASSOCIATIVE;
		case BITIMPLIES -> Associativity.RIGHT_ASSOCIATIVE;
		case BITXOR -> Associativity.LEFT_ASSOCIATIVE;

		// comparison operators
		case COMPGEQ, COMPGT, COMPLEQ, COMPLT -> Associativity.NO_ASSOCIATIVITY;
		case COMPEQ, COMPNEQ -> Associativity.NO_ASSOCIATIVITY;

		case BITSHIFTLEFT, BITSHIFTRIGHT -> Associativity.LEFT_ASSOCIATIVE;

		// TODO is this ok for (i) floating-point types, and (ii) in the presence of overflows? (otherwise use LEFT)
		case ARITHMUL, ARITHPLUS -> Associativity.ASSOCIATIVE;

		case ARITHDIV, ARITHMINUS, ARITHMOD -> Associativity.LEFT_ASSOCIATIVE;
		case LTLUNTIL, LTLWEAKUNTIL, LTLRELEASE -> Associativity.LEFT_ASSOCIATIVE;

		// safe fallback: no associativity
		case BITVECCONCAT, COMPPO -> Associativity.NO_ASSOCIATIVITY;
		};
	}

	private enum Associativity {
		// a <op> b <op> c == (a <op> b) <op> c == a <op> (b <op> c)
		ASSOCIATIVE,
		// a <op> b <op> c == (a <op> b) <op> c
		LEFT_ASSOCIATIVE,
		// a <op> b <op> c == a <op> (b <op> c)
		RIGHT_ASSOCIATIVE,
		// none of the above
		NO_ASSOCIATIVITY;

		public boolean satisfies(final Associativity other) {
			return this == ASSOCIATIVE || other == NO_ASSOCIATIVITY || this == other;
		}
	}

	// cf. ACSL standard, section 2.2.1
	// (note that the order of declaration is crucial for this enum!)
	private enum Precedence {
		BOTTOM,

		NAMING, BINDING, TERNARY, EQUIV, IMPLIES,

		// We pretend &&, ^^ and || have the same precedence, so that parentheses are added for clarity:
		// Instead of "A && B || C && D", we print "(A && B) || (C && D)".
		OR_XOR_AND,

		BIT_EQUIV, BIT_IMPLIES, BIT_OR, BIT_XOR, BIT_AND, EQUALITY, COMPARISON, SHIFT, ADDITIVE, MULTIPLICATIVE,
		LTL_INFIX, UNARY, SELECTION,

		TOP
	}
}
