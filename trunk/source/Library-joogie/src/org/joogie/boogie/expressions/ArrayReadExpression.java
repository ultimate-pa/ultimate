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

import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogieType;
import org.joogie.util.Log;

/**
 * @author schaef
 */
public class ArrayReadExpression extends Expression {

	private Expression baseExpression;
	private Expression idxExpression;

	public ArrayReadExpression(Expression base, Expression idx) {
		baseExpression = base;
		idxExpression = idx;
	}

	public Expression getBaseExpression() {
		return this.baseExpression;
	}

	public Expression getIndexExpression() {
		return this.idxExpression;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#toBoogie()
	 */
	@Override
	public String toBoogie() {
		StringBuilder sb = new StringBuilder();
		sb.append(baseExpression.toBoogie());
		sb.append("[");
		sb.append(idxExpression.toBoogie());
		sb.append("]");
		return sb.toString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#getType()
	 */
	@Override
	public BoogieType getType() {
		if (baseExpression.getType() instanceof BoogieArrayType) {
			return ((BoogieArrayType) (baseExpression.getType()))
					.getNestedType();
		}
		Log.error("Cannot resolve ArrayType");
		return null;
	}

	@Override
	public Expression clone() {
		return new ArrayReadExpression(baseExpression.clone(),
				idxExpression.clone());
	}

	@Override
	public List<Variable> getUsedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		ret.addAll(this.baseExpression.getUsedVariables());
		ret.addAll(this.idxExpression.getUsedVariables());
		return ret;
	}

}
