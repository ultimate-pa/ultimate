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
import java.util.Stack;

import org.joogie.boogie.expressions.Variable;

/**
 * @author schaef
 */
public class HavocStatement extends Statement {

	private Collection<Variable> havocVars;

	public HavocStatement(Collection<Variable> havocvars) {
		this.havocVars = havocvars;
	}

	public Collection<Variable> getHavocVars() {
		return this.havocVars;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.statements.Statement#toBoogie()
	 */
	@Override
	public String toBoogie() {
		StringBuilder sb = new StringBuilder();

		sb.append("havoc ");
		boolean firstround = true;
		for (Variable v : havocVars) {
			if (firstround) {
				firstround = false;
			} else {
				sb.append(", ");
			}
			sb.append(v.toBoogie());
		}
		return sb.toString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.statements.Statement#clone()
	 */
	@Override
	public Statement clone() {
		Stack<Variable> clonevars = new Stack<Variable>();
		for (Variable v : this.havocVars) {
			clonevars.push((Variable) v.clone());
		}
		return new HavocStatement(clonevars);
	}

	@Override
	public List<Variable> getUsedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		ret.addAll(this.havocVars);
		return ret;
	}

	@Override
	public List<Variable> getModifiedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		ret.addAll(this.havocVars);
		return ret;
	}

}
