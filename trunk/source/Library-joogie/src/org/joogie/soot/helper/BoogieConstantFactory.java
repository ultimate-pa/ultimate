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

package org.joogie.soot.helper;

import java.util.HashMap;
import java.util.Map;

import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.Expression;

import soot.PrimType;
import soot.Type;
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

	private final Map<String, Expression> mStringConstantsCache;
	private final Map<Double, Expression> mRealConstantsCache;
	private final BoogieProgramConstructionDecorator mProg;

	BoogieConstantFactory(BoogieProgramConstructionDecorator prog) {
		mStringConstantsCache = new HashMap<String, Expression>();
		mRealConstantsCache = new HashMap<Double, Expression>();
		mProg = prog;
	}

	public Expression createConst(DoubleConstant c) {
		return getRealConstant((double) c.value, (PrimType) c.getType());
	}

	public Expression createConst(FloatConstant c) {
		return getRealConstant((double) c.value, (PrimType) c.getType());
	}

	public Expression createConst(IntConstant c) {
		return new UboundedIntConstant((long) c.value);
	}

	public Expression createConst(LongConstant c) {
		return new UboundedIntConstant(c.value);
	}

	public Expression createConst(int c) {
		return new UboundedIntConstant((long) c);
	}

	public Expression createConst(NullConstant c) {
		return mProg.getNullVariable();
	}

	public Expression createConst(StringConstant c) {
		return getStringConstant(c.value, c.getType());
	}

	public Expression createConst(ClassConstant c) {
		return mProg.getFreshGlobalConstant(mProg.getTypeFactory().lookupBoogieType(c.getType()));
	}

	public Expression getStringConstant(String c, Type t) {
		if (!mStringConstantsCache.containsKey(c)) {
			mStringConstantsCache.put(c, mProg.getFreshGlobalConstant(mProg.getTypeFactory().lookupBoogieType(t)));
		}
		return mStringConstantsCache.get(c);
	}

	// TODO: this will cause float and double to be different types -> FIX
	public Expression getRealConstant(Double c, PrimType t) {
		if (!mRealConstantsCache.containsKey(c)) {
			// TODO the variable should be const unique
			mRealConstantsCache.put(c, mProg.getFreshGlobalConstant(mProg.getTypeFactory().lookupBoogieType(t)));
		}
		return mRealConstantsCache.get(c);
	}

}
