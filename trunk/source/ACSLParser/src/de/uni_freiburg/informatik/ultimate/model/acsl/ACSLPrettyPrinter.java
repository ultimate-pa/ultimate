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
		case final ACSLResultExpression res -> "\\result";
		case final ArrayAccessExpression arrayAccess ->
				"%s[%s]".formatted(printExpression(arrayAccess.getArray()), printExpression(arrayAccess.getIndex()));
		case final AtLabelExpression at -> "\\at(%s, %s)".formatted(printExpression(at.getExpression()), at.getLabel());
		case final BaseAddrExpression base -> "\\base_addr{%s}".formatted(printExpression(base.getExpression()));
		case final BinaryExpression bin -> printBinaryExpression(bin);
		case final BlockLengthExpression block ->
				"\\block_length{%s}".formatted(printExpression(block.getExpression()));
		case final BooleanLiteral boolLit -> "\\" + boolLit.getValue();
		case final CastExpression cast ->
				"(%s) %s".formatted(cast.getCastedType().getTypeName(), printExpression(cast.getExpression()));
		case final FieldAccessExpression f -> "(%s).%s".formatted(printExpression(f.getStruct()), f.getField());
		case final FreeableExpression freeable -> "\\freeable{%s}".formatted(printExpression(freeable.getExpression()));
		case final FunctionApplication function -> "%s(%s)".formatted(function.getIdentifier(),
				Arrays.stream(function.getArguments()).map(x -> printExpression(x)).collect(Collectors.joining(", ")));
		case final IdentifierExpression id -> id.getIdentifier();
		case final IfThenElseExpression ite -> "(%s ? %s : %s)".formatted(printExpression(ite.getCondition()),
				printExpression(ite.getThenPart()), printExpression(ite.getElsePart()));
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
				"%s : %s".formatted(naming.getIdentifier(), printExpression(naming.getExpression()));
		case final UnaryExpression unary -> printUnaryExpression(unary);
		case final ValidExpression valid -> "\\valid(%s)".formatted(printExpression(valid.getExpression()));
		};
	}

	private static String printQuantifierExpression(final QuantifierExpression quantifier) {
		final String quantor = quantifier.isUniversal() ? "\\forall" : "\\exists";
		final String vars = Arrays.stream(quantifier.getVariables())
				.map(x -> x.getType().getTypeName() + " " + x.getName()).collect(Collectors.joining(", "));
		return "%s %s; %s".formatted(quantor, vars, printExpression(quantifier.getSubformula()));
	}

	private static String printUnaryExpression(final UnaryExpression expression) {
		return unaryOperatorToString(expression.getOperator()) + printExpression(expression.getExpr());
	}

	// TODO: Check the operator precedence to avoid unnecessary parentheses
	private static String printBinaryExpression(final BinaryExpression expression) {
		final String op = binaryOperatorToString(expression.getOperator());
		final String left = printExpression(expression.getLeft());
		final String right = printExpression(expression.getRight());
		return String.format("(%s %s %s)", left, op, right);
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
}
