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

import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.types.BoogieFieldType;
import org.joogie.boogie.types.BoogieType;
import org.joogie.util.Log;

/**
 * @author schaef
 */
public class SimpleHeapAccess extends Expression {

	private Expression baseExpression = null;
	private Expression fieldReference = null;
	private Variable heapVariable = null;

	public SimpleHeapAccess(Expression base, Expression field) {
		this(BoogieProgram.v().heapVariable, base, field);
	}

	public SimpleHeapAccess(Variable heapVar, Expression base, Expression field) {
		baseExpression = base;
		fieldReference = field;
		heapVariable = heapVar;
	}

	@Override
	public Expression clone() {
		return new SimpleHeapAccess(this.baseExpression.clone(),
				this.fieldReference.clone());
	}

	public Variable getHeapVariable() {
		return this.heapVariable;
	}

	public Expression getBaseExpression() {
		return this.baseExpression;
	}

	public Expression getFieldExpression() {
		return this.fieldReference;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#toBoogie()
	 */
	@Override
	public String toBoogie() {
		// TODO Auto-generated method stub
		StringBuilder sb = new StringBuilder();
		sb.append(this.heapVariable.toBoogie() + "[");
		sb.append(baseExpression.toBoogie());
		sb.append(", ");
		sb.append(fieldReference.toBoogie());
		sb.append("]");
		return sb.toString();
	}

	public BoogieType getType() {
		if (fieldReference.getType() instanceof BoogieFieldType) {
			return ((BoogieFieldType) fieldReference.getType()).getNestedType();
		} else {
			Log.error("SimpleHeapAccess.java: " + fieldReference.toBoogie()
					+ " : " + fieldReference.getType().getName()
					+ " is not a valid heap field");
		}
		return fieldReference.getType();
	}

	public List<Variable> getUsedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		ret.add(heapVariable); // remember, the order matters!
		ret.addAll(this.baseExpression.getUsedVariables());
		ret.addAll(this.fieldReference.getUsedVariables());
		return ret;
	}

}
