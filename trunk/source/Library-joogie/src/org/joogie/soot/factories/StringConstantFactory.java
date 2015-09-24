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

package org.joogie.soot.factories;

import java.util.HashMap;

import org.joogie.boogie.expressions.Expression;

import soot.Type;

/**
 * TODO: improve
 * 
 * @author schaef
 */
public class StringConstantFactory {

	public static void resetFactory() {
		stringConstants = new HashMap<String, Expression>();
	}

	private static HashMap<String, Expression> stringConstants = new HashMap<String, Expression>();

	public static Expression getStringConstant(String c, Type t) {
		if (!stringConstants.containsKey(c)) {
			stringConstants.put(
					c,
					BoogieVariableFactory.v().getFreshGlobalConstant(
							BoogieTypeFactory.lookupBoogieType(t)));
		}
		return stringConstants.get(c);
	}

}
