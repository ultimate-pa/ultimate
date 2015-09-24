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

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.InvokeExpression;
import org.joogie.boogie.expressions.Variable;

/**
 * @author schaef
 */
public class InvokeStatement extends Statement {

	private InvokeExpression invokeExpr = null;
	private List<Expression> returnTargets = null;

	public InvokeStatement(InvokeExpression exp, List<Expression> returntargets) {
		invokeExpr = exp;
		returnTargets = returntargets;
	}

	public List<Expression> getReturnTargets() {
		return returnTargets;
	}

	public Collection<Variable> getModifiedVars() {
		return this.invokeExpr.getModifiedVars();
	}

	public BoogieProcedure getInvokedProcedure() {
		return invokeExpr.getInvokedProcedure();
	}

	public List<Expression> getArguments() {
		return this.invokeExpr.getArguments();
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
		sb.append("\t call ");
		if (returnTargets.size() > 0) {
			boolean firstround = true;
			for (Expression e : returnTargets) {
				if (firstround) {
					firstround = false;
				} else {
					sb.append(", ");
				}
				sb.append(e.toBoogie());
			}
			sb.append(" := ");
		}
		sb.append(invokeExpr.toBoogie());
		return sb.toString();
	}

	@Override
	public Statement clone() {
		InvokeExpression cexp = (InvokeExpression) this.invokeExpr.clone();
		LinkedList<Expression> creturntargets = new LinkedList<Expression>();
		for (Expression e : returnTargets) {
			creturntargets.add(e.clone());
		}
		Statement ret = new InvokeStatement(cexp, creturntargets);
		ret.setLocationTag(locationTag);
		return ret;
	}

	@Override
	public List<Variable> getUsedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		for (Expression e : this.returnTargets) {
			ret.addAll(e.getUsedVariables());
		}
		ret.addAll(this.invokeExpr.getUsedVariables());
		return ret;
	}

	@Override
	public List<Variable> getModifiedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		for (Expression e : this.returnTargets) {
			ret.addAll(tmpGetWrittenVar(e));
		}
		ret.addAll(this.invokeExpr.getModifiedVars());
		return ret;
	}

}
