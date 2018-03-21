/*
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 *
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea;

import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.armc.ARMCWriter.ARMCString;

/**
 * RelationDecision is an extension of BooleanDecision and represents a simple relational statement. Currently (in the
 * context of the PEA toolkit with its export functions to, e.g., ARMC) we support expression with basic arithmetical
 * relations: <,>,<=,>=,=,!=. For instance, the boolean expression a < b+c can be processed (b+c is considered as a
 * constant). More complicated expressions are not supported. Please use ZDecision instead.
 *
 * @author jfaber
 */
public class RelationDecision extends BooleanDecision {

	public enum Operator {
		/*
		 * Constants for supported operators in BooleanDecisions. We use the ARMC strings as default where possible.
		 */
		PRIME("'"), LESS(ARMCString.LESS), GREATER(ARMCString.GREATER), LEQ(ARMCString.LEQ), GEQ(ARMCString.GEQ),
		EQUALS(ARMCString.EQUALS), PLUS(ARMCString.PLUS), MINUS(ARMCString.MINUS), MULT(ARMCString.MULT),
		DIV(ARMCString.DIV), NEQ("!=");

		String op;

		private Operator(final String op) {
			this.op = op;
		}

		@Override
		public String toString() {
			return op;
		}

	}

	String leftExpr;
	String rightExpr;
	Operator op;

	/**
	 * @param leftExpr
	 * @param op
	 * @param rightExpr
	 */
	public RelationDecision(final String leftExpr, final Operator op, final String rightExpr) {
		super(leftExpr + op + rightExpr);
		if (leftExpr == null || rightExpr == null) {
			System.err.println();
		}
		this.leftExpr = leftExpr;
		this.op = op;
		this.rightExpr = rightExpr;
	}

	/**
	 * Create an boolean constraint.
	 *
	 * @param mVar
	 *            the condition that must hold.
	 */
	public static CDD create(final String leftExpr, final Operator op, final String rightExpr) {
		if (op.equals(Operator.GEQ)) {
			return CDD.create(new RelationDecision(leftExpr, Operator.LESS, rightExpr), CDD.FALSE_CHILDS);
		} else if (op.equals(Operator.GREATER)) {
			return CDD.create(new RelationDecision(leftExpr, Operator.LEQ, rightExpr), CDD.FALSE_CHILDS);
		}
		return CDD.create(new RelationDecision(leftExpr, op, rightExpr), CDD.TRUE_CHILDS);
	}

	/**
	 * Returns a RelationDecision for the given operator and the given expressions contained in the array exprs.
	 *
	 * @param exprs
	 *            Left and right expression for the given binary operator. Throws a IllegalArgumentException() when
	 *            exprs has not exactly two entries.
	 * @param op
	 *            The binary operator for the expression.
	 * @return RelationDecision for the operator and the given expressions.
	 */
	public static CDD create(final String[] exprs, final Operator op) {
		if (exprs.length != 2) {
			throw new IllegalArgumentException();
		}
		return RelationDecision.create(exprs[0], op, exprs[1]);
	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof BooleanDecision)) {
			return false;
		}
		return getVar().equals(((BooleanDecision) o).getVar());
	}

	@Override
	public String toString(final int child) {
		if (child != 0) {
			switch (op) {
			case LESS:
				return leftExpr + Operator.GEQ + rightExpr;
			case GREATER:
				return leftExpr + Operator.LEQ + rightExpr;
			case LEQ:
				return leftExpr + Operator.GREATER + rightExpr;
			case GEQ:
				return leftExpr + Operator.LESS + rightExpr;
			case EQUALS:
				return leftExpr + Operator.NEQ + rightExpr;
			case NEQ:
				return leftExpr + Operator.EQUALS + rightExpr;
			default:
				break;
			}
		}
		return getVar();
	}

	@Override
	public String toUppaalString(final int child) {
		return "true";
	}

	@Override
	public RelationDecision prime() {
		final String expr1 = leftExpr.replaceAll("([a-zA-Z_])(\\w*)", "$1$2" + BooleanDecision.PRIME_SUFFIX);
		final String expr2 = rightExpr.replaceAll("([a-zA-Z_])(\\w*)", "$1$2" + BooleanDecision.PRIME_SUFFIX);
		return (new RelationDecision(expr1, op, expr2));
	}

	@Override
	public RelationDecision unprime() {
		String expr1 = leftExpr;
		String expr2 = rightExpr;
		if (leftExpr.endsWith(PRIME_SUFFIX)) {
			expr1 = leftExpr.substring(0, leftExpr.length() - 1);
		}
		if (rightExpr.endsWith(PRIME_SUFFIX)) {
			expr2 = rightExpr.substring(0, rightExpr.length() - 1);
		}
		return (new RelationDecision(expr1, op, expr2));
	}
}
