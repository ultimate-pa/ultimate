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

import java.util.List;

import org.joogie.boogie.types.BoogieType;

/**
 * @author schaef
 */
public abstract class Expression {

	@Override
	public String toString() {
		return this.toBoogie();
	}

	public abstract String toBoogie();

	public abstract BoogieType getType();

	@Override
	public abstract Expression clone();

	/*
	 * TODO: note that when you implement this procedure, the order matters as
	 * this procedure is used to create the list of input parameters for pure
	 * methods. If you screw up the order, your prelude will be wrong and
	 * horrible things will happen to you and your beloved ones!
	 */
	public abstract List<Variable> getUsedVariables();
}
