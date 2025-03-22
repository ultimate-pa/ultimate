/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ACSLParser plug-in.
 *
 * The ULTIMATE ACSLParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ACSLParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ACSLParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ACSLParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ACSLParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.model.acsl;

import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLVisitor;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;

/**
 * Preliminary ACSL LTL extension pretty printer.
 *
 * @author dietsch@informatik.uni-freiburg.de
 */
public class LTLPrettyPrinter extends ACSLVisitor {
	private static final String GET_STRING = "getString(";
	private static final String NOT_IMPLEMENTED = ") not implemented";

	private static final String STRING_AND = "&";
	private static final String STRING_MINUS = "-";
	private static final String STRING_TIMES = "*";
	private static final String STRING_PLUS = "+";

	private static final char BLANK = ' ';
	private static final char PARENTHESIS_CLOSE = ')';
	private static final char PARENTHESIS_OPEN = '(';

	protected StringBuilder mBuilder;

	/**
	 * @param node
	 *            Node.
	 * @return string representation
	 */
	public String print(final ACSLNode node) {
		mBuilder = new StringBuilder();
		node.accept(this);
		return mBuilder.toString();
	}

	@Override
	public boolean visit(final BinaryExpression node) {
		mBuilder.append(PARENTHESIS_OPEN);
		node.getLeft().accept(this);
		mBuilder.append(BLANK).append(getString(node.getOperator())).append(BLANK);
		node.getRight().accept(this);
		mBuilder.append(PARENTHESIS_CLOSE);
		return false;
	}

	@Override
	public boolean visit(final UnaryExpression node) {
		mBuilder.append(getString(node.getOperator())).append('(');
		node.getExpr().accept(this);
		mBuilder.append(')');
		return false;
	}

	@Override
	public boolean visit(final BooleanLiteral node) {
		mBuilder.append(node.getValue());
		return super.visit(node);
	}

	@Override
	public boolean visit(final IdentifierExpression node) {
		mBuilder.append(node.getIdentifier());
		return super.visit(node);
	}

	@Override
	public boolean visit(final IntegerLiteral node) {
		mBuilder.append(node.getValue());
		return super.visit(node);
	}

	@Override
	public boolean visit(final RealLiteral node) {
		mBuilder.append(node.getValue());
		return super.visit(node);
	}

	private static String getString(final UnaryExpression.Operator operator) {
		return switch (operator) {
		case ADDROF -> STRING_AND;
		case LOGICNEG -> "!";
		case LTLFINALLY -> "F";
		case LTLGLOBALLY -> "G";
		case LTLNEXT -> "X";
		case MINUS -> STRING_MINUS;
		case PLUS -> STRING_PLUS;
		case POINTER -> STRING_TIMES;
		case LOGICCOMPLEMENT -> throw new UnsupportedOperationException(GET_STRING + operator + NOT_IMPLEMENTED);
		};
	}

	private static String getString(final Operator operator) {
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
		case LTLUNTIL -> "U";
		case LTLRELEASE -> "R";
		case LTLWEAKUNTIL -> "WU";
		case LOGICXOR, COMPPO, BITXOR, BITVECCONCAT, BITSHIFTLEFT, BITSHIFTRIGHT ->
				throw new UnsupportedOperationException(GET_STRING + operator + NOT_IMPLEMENTED);
		};
	}
}
