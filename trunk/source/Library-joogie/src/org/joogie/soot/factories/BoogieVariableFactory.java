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

import java.util.LinkedList;

import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieType;
import org.joogie.soot.BoogieHelpers;
import org.joogie.soot.GlobalsCache;

/**
 * @author schaef
 */
public class BoogieVariableFactory {

	// TODO only a stub needed by getFreshVariable
	private Integer freshVarCounter = 0;

	/**
	 * Singleton object
	 */
	private static BoogieVariableFactory instance = null;

	/**
	 * C-tor
	 */
	private BoogieVariableFactory() {
		// do nothing
	}

	/**
	 * Returns the Singleton object
	 * 
	 * @return Singleton object
	 */
	public static BoogieVariableFactory v() {
		if (null == instance) {
			instance = new BoogieVariableFactory();
		}
		return instance;
	}

	/**
	 * Resets the Singleton
	 */
	public static void resetInstance() {
		instance = null;
	}

	public Expression getFreshLocalVariable(BoogieType t) {
		return getFreshLocalVariable("$freshlocal", t);
	}

	public Variable getFreshLocalVariable(String prefix, BoogieType t) {
		return BoogieHelpers.currentProcedure.getFreshLocalVariable(prefix, t);
	}

	public Expression getFreshGlobalConstant(BoogieType t) {
		Variable v = new Variable("$fresh" + (++freshVarCounter).toString(), t);
		BoogieProgram.v().addGlobalVar(v);
		return v;
	}

	public Expression getFreshHeapField(soot.Type t) {
		Expression exp = BoogieVariableFactory.v()
				.createNewHeapVariable();
		return OperatorFunctionFactory.v().castIfNecessary(exp,
				BoogieTypeFactory.lookupBoogieType(t));
	}

	public Expression createNewHeapVariable() {
		LinkedList<Expression> args = new LinkedList<Expression>();
		args.add(BoogieConstantFactory.createConst(GlobalsCache.v()
				.getUniqueNumber()));
		return BoogieHelpers.createInvokeExpression(OperatorFunctionFactory.v().getNewVarProcedure(), args);
	}
	
	
	public Variable createBoogieVariable(String name, BoogieType t,
			boolean isunique) {
		return new Variable(name, t, isunique);
	}



}
