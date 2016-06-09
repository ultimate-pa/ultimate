/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;

/**
 * 
 * @author Alexander Nutz, Matthias Heizmann
 *
 */
public abstract class LRValue {
	
	/**
	 * Abstract class constructor -- all inheritors of LRValue have at least
	 * an expression representing what the containing result evaluates to.
	 * @param value
	 */
	public LRValue (CType cType, boolean isBoogieBool, boolean isIntFromPointer) {
		this.cType = cType;
		this.isBoogieBool = isBoogieBool;
		this.isIntFromPointer = isIntFromPointer;
	}
	
	private final CType cType;
	
	/** 
	 * This flag is supposed to be true iff the value-expression of this
	 * LRValue is of boolean type in boogie.  
	 * For instance if it is the translation of a comparator expression
	 * like x == 0.
	 */
	private final boolean isBoogieBool;

	private final boolean isIntFromPointer;

	
	public abstract Expression getValue();
	
	public CType getCType() {
		return cType;
	}

	public boolean isBoogieBool() {
		return isBoogieBool;
	}

	public boolean isIntFromPointer() {
		return isIntFromPointer;
	}

	@Override
	public final String toString() {
		if (this instanceof HeapLValue) {
			return "address: " + ((HeapLValue) this).getAddress();
		} else if (this instanceof LocalLValue) {
			return "lhs: " + ((LocalLValue) this).getLHS();
		} else {
			return "value: " + getValue();
		}
	}

}
