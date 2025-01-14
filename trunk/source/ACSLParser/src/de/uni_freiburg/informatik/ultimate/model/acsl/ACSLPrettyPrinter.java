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
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CastExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnotStmt;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Ensures;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FieldAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GhostDeclaration;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalGhostDeclaration;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.OldValueExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Requires;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ValidExpression;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ACSLPrettyPrinter {
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
		switch (expression) {
		case final BooleanLiteral boolLit:
			return "\\" + boolLit.getValue();
		case final IntegerLiteral intLit:
			return intLit.getValue();
		case final RealLiteral realLit:
			return realLit.getValue();
		case final IdentifierExpression id:
			return id.getIdentifier();
		case final BinaryExpression bin:
			return printBinaryExpression(bin);
		case final UnaryExpression unary:
			return printUnaryExpression(unary);
		case final IfThenElseExpression ite:
			return String.format("(%s ? %s : %s)", printExpression(ite.getCondition()),
					printExpression(ite.getThenPart()), printExpression(ite.getElsePart()));
		case final ValidExpression valid:
			return String.format("\\valid(%s)", printExpression(valid.getFormula()));
		case final FieldAccessExpression f:
			return String.format("(%s).%s", printExpression(f.getStruct()), f.getField());
		case final OldValueExpression old:
			return String.format("\\old(%s)", printExpression(old.getFormula()));
		case final ArrayAccessExpression arrayAccess:
			return printArrayAccessExpression(arrayAccess);
		case final CastExpression cast:
			return String.format("(%s) %s", cast.getCastedType().getTypeName(), printExpression(cast.getExpression()));
		case final ACSLResultExpression res:
			return "\\result";
		case final AtLabelExpression at:
			return String.format("\\at(%s, %s)", printExpression(at.getFormula()), at.getLabel());
		default:
			// TODO: Add more cases
			return expression.toString();
		}
	}

	private static String printArrayAccessExpression(final ArrayAccessExpression expression) {
		return printExpression(expression.getArray()) + "["
				+ Arrays.stream(expression.getIndices()).map(x -> printExpression(x)).collect(Collectors.joining(", "))
				+ "]";
	}

	private static String printUnaryExpression(final UnaryExpression expression) {
		final String op;
		switch (expression.getOperator()) {
		case ADDROF:
			op = "&";
			break;
		case LOGICCOMPLEMENT:
			op = "~";
			break;
		case LOGICNEG:
			op = "!";
			break;
		case MINUS:
			op = "-";
			break;
		case PLUS:
			op = "+";
			break;
		case POINTER:
			op = "*";
			break;
		default:
			throw new AssertionError("Unhandled operator " + expression.getOperator());
		}
		return op + printExpression(expression.getExpr());
	}

	// TODO: Check the operator precedence to avoid unnecessary parentheses
	private static String printBinaryExpression(final BinaryExpression expression) {
		final String op;
		switch (expression.getOperator()) {
		case ARITHDIV:
			op = "/";
			break;
		case ARITHMINUS:
			op = "-";
			break;
		case ARITHMOD:
			op = "%";
			break;
		case ARITHMUL:
			op = "*";
			break;
		case ARITHPLUS:
			op = "+";
			break;
		case BITAND:
			op = "&";
			break;
		case BITIFF:
			op = "<-->";
			break;
		case BITIMPLIES:
			op = "-->";
			break;
		case BITOR:
			op = "|";
			break;
		case BITXOR:
			op = "^";
			break;
		case COMPEQ:
			op = "==";
			break;
		case COMPGEQ:
			op = ">=";
			break;
		case COMPGT:
			op = ">";
			break;
		case COMPLEQ:
			op = "<=";
			break;
		case COMPLT:
			op = "<";
			break;
		case COMPNEQ:
			op = "!=";
			break;
		case LOGICAND:
			op = "&&";
			break;
		case LOGICIFF:
			op = "<==>";
			break;
		case LOGICIMPLIES:
			op = "==>";
			break;
		case LOGICOR:
			op = "||";
			break;
		case LOGICXOR:
			op = "^^";
			break;
		case BITSHIFTLEFT:
			op = "<<";
			break;
		case BITSHIFTRIGHT:
			op = ">>";
			break;
		default:
			throw new AssertionError("Unhandled operator " + expression.getOperator());
		}
		final String left = printExpression(expression.getLeft());
		final String right = printExpression(expression.getRight());
		return String.format("(%s %s %s)", left, op, right);
	}
}
