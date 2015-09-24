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

package org.joogie.ssa;

import java.util.List;

import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieType;

/**
 * @author schaef
 */
public class SSAVariable extends Variable {

	protected Variable var;
	protected int incarnation;

	public SSAVariable(Variable v, int inc) {
		/*
		 * This is a hack ... actually, SsaVariable is not really a subtype of
		 * Variable. We should extract a common interface. However, for now,
		 * this does not harm anyone.
		 */
		super(v.getName(), v.getType());
		this.var = v;
		this.incarnation = inc;
	}

	public int getIncarnation() {
		return this.incarnation;
	}

	public Variable getOriginalVar() {
		return this.var;
	}

	@Override
	public String getName() {
		StringBuilder sb = new StringBuilder();
		sb.append(this.var.getName());
		sb.append("__");
		sb.append(this.incarnation);
		return sb.toString();
	}

	@Override
	public String toBoogie() {
		StringBuilder sb = new StringBuilder();
		sb.append(this.var.getName());
		sb.append("__");
		sb.append(this.incarnation);
		return sb.toString();
	}

	@Override
	public BoogieType getType() {
		return this.var.getType();
	}

	@Override
	public boolean isConstUnique() {
		return this.var.isConstUnique();
	}

	@Override
	public Variable clone() {
		return new SSAVariable(this.var, this.incarnation);
	}

	@Override
	public List<Variable> getUsedVariables() {
		// TODO: check if this makes sense. So far, it should not be used at
		// all.
		return this.var.getUsedVariables();
	}

}
