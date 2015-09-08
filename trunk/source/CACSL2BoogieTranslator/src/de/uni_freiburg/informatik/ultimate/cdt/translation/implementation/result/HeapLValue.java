/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;

public class HeapLValue extends LRValue {

	/**
	 * A Value inside a ResultExpression that represents a position on the
	 * heap. Its value may be either the address or the contents of the heap
	 * position.
	 * @param address
	 * @param addressIsValue determines whether the value of this is currently an address
	 * or a Expression
	 */
	public HeapLValue(Expression address, CType cType) {
		this(address, cType, false);
	}

	public HeapLValue(Expression address, CType cType, boolean isIntFromPtr) {
		super(cType, false, isIntFromPtr);
		this.address = address;
	}
	Expression address;
	
	public Expression getAddress() {
		return this.address;
	}
	
	public Expression getValue() {
		throw new AssertionError("HeapLValues must be converted to RValue before their value can be queried.");
	}
}
