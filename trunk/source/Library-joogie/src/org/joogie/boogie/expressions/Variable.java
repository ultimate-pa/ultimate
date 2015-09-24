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

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.joogie.boogie.types.BoogieType;

/**
 * @author schaef
 */
public class Variable extends Expression {

	private String varName = "TestVar";
	private BoogieType varType;
	private boolean constUnique = false;

	public boolean isBound = false;

	public Variable(String name, BoogieType t) {
		varName = name;
		varType = t;
	}

	public Variable(String name, BoogieType t, boolean constunique) {
		varName = name;
		varType = t;
		constUnique = constunique;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Variable#getName()
	 */
	public String getName() {
		return varName;
	}

	public void setName(String name) {
		varName = name;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Variable#isConstUnique()
	 */
	public boolean isConstUnique() {
		return constUnique;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Variable#clone()
	 */
	@Override
	public Variable clone() {
		return this;
		// TODO: I guess variables should not be cloned because otherwise,
		// we loose the mapping between the instance and it's declaration
		// which causes problems during SSA
		// return new Variable(this.varName, this.varType, this.constUnique);
	}

	// TODO should we introduce getType for all expression? then we can do
	// TypeChecking.
	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Variable#getType()
	 */
	@Override
	public BoogieType getType() {
		return varType;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#toBoogie()
	 */
	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Variable#toBoogie()
	 */
	@Override
	public String toBoogie() {
		return varName;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Variable#getUsedVariables()
	 */
	@Override
	public List<Variable> getUsedVariables() {
		return new LinkedList<Variable>(Arrays.asList(new Variable[] { this }));
	}

}
