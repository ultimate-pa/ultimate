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

package org.joogie.boogie.statements;

import java.util.LinkedList;
import java.util.List;

import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;

/**
 * Expression statements are only used for prelude functions right now. Don't
 * try to use them for something else as this has not been tested.
 * 
 * @author schaef
 */
public class ExpressionStatement extends Statement {

	private Expression expr;

	public ExpressionStatement(Expression e) {
		this.expr = e;
	}

	public Expression getExpression() {
		return this.expr;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.statements.Statement#toBoogie()
	 */
	@Override
	public String toBoogie() {
		return this.expr.toBoogie();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.statements.Statement#clone()
	 */
	@Override
	public Statement clone() {
		return new ExpressionStatement(this.expr.clone());
	}

	@Override
	public List<Variable> getUsedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		ret.addAll(this.expr.getUsedVariables());
		return ret;
	}

	@Override
	public List<Variable> getModifiedVariables() {
		return new LinkedList<Variable>();
	}

}
