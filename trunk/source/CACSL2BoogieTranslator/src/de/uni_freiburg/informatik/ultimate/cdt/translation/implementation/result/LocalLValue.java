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

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;

public class LocalLValue extends LRValue {

	public LeftHandSide lhs;

	/**
	 * A Value inside a ResultExpression that is not stored on the heap, but as
	 * a normal Boogie Variable. It may be written (call getLHS()) or read (by
	 * making it to an RValue first).
	 * 
	 * @param expr
	 */
	public LocalLValue(LeftHandSide lhs, CType cType) {
		this(lhs, cType, false, false);
	}
	
	public LocalLValue(LeftHandSide lhs, CType cType, boolean isBoogieBool) {
		this(lhs, cType, isBoogieBool, false);
	}

	public LocalLValue(LeftHandSide lhs, CType cType, boolean isBoogieBool, boolean isIntFromPtr) {
		super(cType, isBoogieBool, isIntFromPtr);
		this.lhs = lhs;
	}

	public LocalLValue(LocalLValue llVal) {
		this(llVal.lhs, llVal.getCType(), llVal.isBoogieBool(), llVal.isIntFromPointer());
	}
	
	public LeftHandSide getLHS() {
		return lhs;
	}

	public Expression getValue() {
		return CHandler.convertLHSToExpression(lhs);
	}
}
