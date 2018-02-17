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
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;

public class LocalLValue extends LRValue {

	public LeftHandSide lhs;
	private final BitfieldInformation mBitfieldInformation;

	/**
	 * A Value inside a ResultExpression that is not stored on the heap, but as
	 * a normal Boogie Variable. It may be written (call getLHS()) or read (by
	 * making it to an RValue first).
	 * 
     * @param bi In case this LocalLValue represents a bit-field this object 
	 * contains additional information. In case this LocalLValue does not 
	 * represent a bit-field we use null.
	 * 
	 * @param expr
	 */
	public LocalLValue(final LeftHandSide lhs, final CType cType, final BitfieldInformation bi) {
		this(lhs, cType, false, false, bi);
		
	}
	
	public LocalLValue(final LeftHandSide lhs, final CType cType, final boolean isBoogieBool) {
		this(lhs, cType, isBoogieBool, false, null);
	}

	public LocalLValue(final LeftHandSide lhs, final CType cType, final boolean isBoogieBool, final boolean isIntFromPtr, final BitfieldInformation bi) {
		super(cType, isBoogieBool, isIntFromPtr);
		this.lhs = lhs;
		mBitfieldInformation = bi;
	}

	public LocalLValue(final LocalLValue llVal) {
		this(llVal.lhs, llVal.getCType(), llVal.isBoogieBool(), llVal.isIntFromPointer(), null);
	}
	
	public LeftHandSide getLHS() {
		return lhs;
	}

	@Override
	public Expression getValue() {
		return CTranslationUtil.convertLHSToExpression(lhs);
	}
	
	public BitfieldInformation getBitfieldInformation() {
		return mBitfieldInformation;
	}
}
