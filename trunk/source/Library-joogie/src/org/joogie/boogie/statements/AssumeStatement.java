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
import org.joogie.boogie.types.BoogieBaseTypes;

/**
 * @author schaef
 */
public class AssumeStatement extends Statement {

	private Expression expression = null;

	public AssumeStatement(Expression exp) {
		expression = exp;
	}

	public Expression getExpression() {
		return expression;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.statements.Statement#toBoogie()
	 */
	@Override
	public String toBoogie() {
		StringBuilder sb = new StringBuilder();
		if (locationTag != null) {
			sb.append(locationTag.toString());
		}
		sb.append("\t assume (");
		sb.append(expression.toBoogie());
		if (expression.getType() == BoogieBaseTypes.getBoolType())
			sb.append(")");
		else
			sb.append("==1)");
		return sb.toString();
	}

	@Override
	public Statement clone() {
		Statement ret = new AssumeStatement(this.expression.clone());
		ret.setLocationTag(locationTag);
		return ret;
	}

	@Override
	public List<Variable> getUsedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		ret.addAll(this.expression.getUsedVariables());
		return ret;
	}

	@Override
	public List<Variable> getModifiedVariables() {
		return new LinkedList<Variable>();
	}

}
