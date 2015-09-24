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

import org.joogie.boogie.types.BoogieType;
import org.joogie.util.Log;

/**
 * WARNING, this is only a Hack. It is only supposed to be used in BoogieAxioms.
 * Joogie represents all Java Bytecode expression as Int Typed to avoid trouble
 * in Boogie caused by implicit casts from Int to Bool. This problem can be
 * lifted by putting more effort in the implementation of
 * OperatorFunctionFactory and BoogieTypeFactory by actually considering Bool as
 * a dedicated type. However, so far there was no time to do this Same problem
 * with org.joogie.boogie.expressions.BooleanExpression
 * 
 * @author schaef
 */
public class IteExpression extends Expression {

	private Expression conditional = null;
	private Expression thenResult = null;
	private Expression elseResult = null;

	public IteExpression(Expression c, Expression t, Expression e) {
		if (c == null || t == null || e == null) {
			Log.error(c + " " + t + " " + e);
			throw new RuntimeException();
		}

		this.conditional = c;
		this.thenResult = t;
		this.elseResult = e;
	}

	public Expression getCond() {
		return this.conditional;
	}

	public Expression getThen() {
		return this.thenResult;
	}

	public Expression getElse() {
		return this.elseResult;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expression.Statement#toBoogie()
	 */
	@Override
	public String toBoogie() {
		StringBuilder sb = new StringBuilder();
		sb.append("if ");
		sb.append(this.conditional.toBoogie());
		sb.append(" then ");
		sb.append(this.thenResult.toBoogie());
		sb.append(" else ");
		sb.append(this.elseResult.toBoogie());
		return sb.toString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expression.Statement#clone()
	 */
	@Override
	public Expression clone() {
		return new IteExpression(this.conditional.clone(),
				this.thenResult.clone(), this.elseResult.clone());
	}

	@Override
	public BoogieType getType() {
		// TODO: this check is for debugging purpose only, can be removed later
		if (this.thenResult.getType() != this.elseResult.getType()) {
			Log.debug("Types do not match in IteExpression");
		}
		return this.thenResult.getType();
	}

	@Override
	public List<Variable> getUsedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		ret.addAll(this.conditional.getUsedVariables());
		ret.addAll(this.thenResult.getUsedVariables());
		ret.addAll(this.elseResult.getUsedVariables());
		return ret;
	}

}
