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
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class Variable extends Expression {

	private String mVarName;
	private final BoogieType mVarType;
	private boolean mIsBound;
	private boolean mIsConstant;
	private boolean mIsUnique;

	public Variable(final String name, final BoogieType t) {
		this(name, t, false);
	}

	public Variable(final String name, final BoogieType type, final boolean constunique) {
		mVarName = name;
		mVarType = type;
		mIsBound = false;
		mIsConstant = constunique;
		mIsUnique = constunique;
	}

	public String getName() {
		return mVarName;
	}

	public void setName(final String name) {
		mVarName = name;
	}

	public void setIsBound(final boolean isBound) {
		mIsBound = isBound;
	}

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
	@Override
	public BoogieType getType() {
		return mVarType;
	}

	@Override
	public String toBoogie() {
		return mVarName;
	}

	@Override
	public List<Variable> getUsedVariables() {
		return new LinkedList<Variable>(Arrays.asList(new Variable[] { this }));
	}

	public boolean isConstUnique() {
		return mIsConstant && mIsUnique;
	}

}
