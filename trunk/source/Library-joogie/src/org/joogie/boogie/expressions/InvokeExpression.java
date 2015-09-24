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

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieType;

/**
 * @author schaef
 */
public class InvokeExpression extends Expression {

	private LinkedList<Expression> arguments;
	private String qualifiedName;
	private BoogieType returnType;
	private BoogieProcedure invokedProcedure;

	// TODO fix BoogieHelperFunctions s.t. we can remove qual_name and
	// returntype because they are already in proc
	public InvokeExpression(BoogieProcedure proc, LinkedList<Expression> args) {
		invokedProcedure = proc;
		qualifiedName = proc.getName();
		if (proc.getReturnVariable() != null) {
			returnType = proc.getReturnVariable().getType();
		} else {
			returnType = BoogieBaseTypes.getVoidType();
		}

		arguments = args;

	}

	public BoogieProcedure getInvokedProcedure() {
		return this.invokedProcedure;
	}

	public Collection<Variable> getModifiedVars() {
		return this.invokedProcedure.modifiesGlobals;
	}

	public List<Expression> getArguments() {
		return this.arguments;
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
		sb.append(qualifiedName + "(");
		boolean first = true;
		for (Expression exp : arguments) {
			if (first) {
				first = false;
			} else {
				sb.append(", ");
			}
			sb.append("(" + exp.toBoogie() + ")");
		}
		sb.append(")");
		return sb.toString();
	}

	public BoogieType getType() {
		return returnType;
	}

	@Override
	public Expression clone() {
		LinkedList<Expression> cargs = new LinkedList<Expression>();
		for (Expression e : arguments) {
			cargs.add(e.clone());
		}
		return new InvokeExpression(this.invokedProcedure, cargs);
	}

	@Override
	public List<Variable> getUsedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		for (Expression e : this.arguments) {
			ret.addAll(e.getUsedVariables());
		}
		ret.addAll(this.getModifiedVars());
		return ret;
	}

}
