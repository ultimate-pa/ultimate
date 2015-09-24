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

import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.Expression;
import org.joogie.soot.BoogieHelpers;

import soot.PrimType;
import soot.jimple.ClassConstant;
import soot.jimple.DoubleConstant;
import soot.jimple.FloatConstant;
import soot.jimple.IntConstant;
import soot.jimple.LongConstant;
import soot.jimple.NullConstant;
import soot.jimple.StringConstant;

/**
 * @author schaef
 */
public class BoogieConstantFactory {

	public static Expression createConst(DoubleConstant c) {
		return RealConstantFactory.getRealConstant((double) c.value,
				(PrimType) c.getType());
	}

	public static Expression createConst(FloatConstant c) {
		return RealConstantFactory.getRealConstant((double) c.value,
				(PrimType) c.getType());
	}

	public static Expression createConst(IntConstant c) {
		return new UboundedIntConstant((long) c.value);
	}

	public static Expression createConst(LongConstant c) {
		return new UboundedIntConstant(c.value);
	}

	public static Expression createConst(int c) {
		return new UboundedIntConstant((long) c);
	}

	public static Expression createConst(NullConstant c) {
		return BoogieHelpers.getNullVariable();
	}

	public static Expression createConst(StringConstant c) {
		return StringConstantFactory.getStringConstant(c.value, c.getType());
	}

	public static Expression createConst(ClassConstant c) {
		return BoogieVariableFactory.v().getFreshGlobalConstant(
				BoogieTypeFactory.lookupBoogieType(c.getType()));
	}

}
