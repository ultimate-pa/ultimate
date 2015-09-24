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

import org.joogie.boogie.LocationTag;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;

/**
 * @author schaef
 */
public abstract class Statement {

	protected LocationTag locationTag = null;

	public void setLocationTag(LocationTag ltag) {
		locationTag = ltag;
	}

	public LocationTag getLocationTag() {
		return this.locationTag;
	}
	
	@Override
	public String toString() {
		return this.toBoogie();
	}

	public abstract String toBoogie();

	@Override
	public abstract Statement clone();

	public abstract List<Variable> getUsedVariables();

	public abstract List<Variable> getModifiedVariables();

	/*
	 * TODO: this method is a hack! when we try to identify the modified
	 * variables using getModifiedVariables, we might encounter array or heap
	 * accesses which have more than one used variable. In this case we only
	 * pick the first one, as we assume that this is the heap/array variable
	 * which is actually written and all other variables are only indices.
	 * However, this is not a reliable way to implement this and it should be
	 * changed in the future.
	 */
	protected List<Variable> tmpGetWrittenVar(Expression e) {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		for (Variable v : e.getUsedVariables()) {
			ret.add(v);
			break;
		}
		return ret;
	}

}
