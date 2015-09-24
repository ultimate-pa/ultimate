/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.boogie.expressions;

import java.util.LinkedList;
import java.util.List;

import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieType;
import org.joogie.util.Log;

/**
 * WARNING, this is only a Hack. It is only supposed to be used in BoogieAxioms.
 * Joogie represents all Java Bytecode expression as Int Typed to avoid trouble
 * in Boogie caused by implicit casts from Int to Bool. This problem can be
 * lifted by putting more effort in the implementation of
 * OperatorFunctionFactory and BoogieTypeFactory by actually considering Bool as
 * a dedicated type. However, so far there was no time to do this Same problem
 * with org.joogie.boogie.expressions.IteExpression
 * 
 * @author schaef
 */
public class BinOpExpression extends Expression {

	private Operator operator;
	private Expression lhs;
	private Expression rhs;

	public enum Operator {
		Eq("=="), Neq("!="), Lt("<"), Le("<="), Gt(">"), Ge(">="), Implies("=>"), LAnd(
				"&&"), LOr("||"), Plus("+"), Minus("-"), Mul("*"), Div("/");
		private String description;

		Operator(String des) {
			description = des;
		}

		@Override
		public String toString() {
			return description;
		}
	}

	public BinOpExpression(Operator op, Expression lhse, Expression rhse) {
		operator = op;
		lhs = lhse;
		rhs = rhse;
	}

	public Expression getLhs() {
		return lhs;
	}

	public Expression getRhs() {
		return rhs;
	}

	public Operator getOp() {
		return operator;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#toBoogie()
	 */
	@Override
	public String toBoogie() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(lhs.toBoogie());
		sb.append(" " + operator + " ");
		sb.append(rhs.toBoogie());
		sb.append(")");
		return sb.toString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#getType()
	 */
	@Override
	public BoogieType getType() {
		switch (this.operator) {
		case Ge:
		case Gt:
		case Lt:
		case Le:
		case Eq:
		case Neq:
		case Implies:
		case LAnd:
		case LOr:
			return BoogieBaseTypes.getBoolType();
		case Div:
		case Minus:
		case Mul:
		case Plus:
			return this.lhs.getType();
		default:
			Log.error("Type resolution failed: " + this.toString());
			return null;
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#clone()
	 */
	@Override
	public Expression clone() {
		return new BinOpExpression(operator, lhs.clone(), rhs.clone());
	}

	@Override
	public List<Variable> getUsedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		ret.addAll(lhs.getUsedVariables());
		ret.addAll(rhs.getUsedVariables());
		return ret;
	}

}
