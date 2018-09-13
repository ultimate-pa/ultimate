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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;

public class HeapLValue extends LRValue {

	private final BitfieldInformation mBitfieldInformation;

	/**
	 * LRValue that stores a memory address.
	 * Two use cases:
	 *  <li> HeapLValue is read: then we will call "switchToRValue" on the ExpressionResult containing this HeapLValue
	 *    first. This will generate  code that reads the memory at the address of this HeapLValue and store it inside a
	 *    temporary variable, which will be the new LRValue of that ExpressionResult.
	 *  <li> HeapLValue is written: then we use the address of this HeapLValue to generate the code that writes to the
	 *    according memory location.
	 *
	 * @param address the memory address
	 * @param cType the type (in terms of C, as opposed to boogie) of the information that is stored at address
	 * @param bi In case this HeapLValue represents a bit-field this object
	 * contains additional information. In case this HeapLValue does not
	 * represent a bit-field we use null.
	 */
	public HeapLValue(final Expression address, final CType cType, final BitfieldInformation bi) {
		this(address, cType, false, bi);
	}

	public HeapLValue(final Expression address, final CType cType, final boolean isIntFromPtr, final BitfieldInformation bi) {
		super(cType, false, isIntFromPtr);
		this.address = address;
		mBitfieldInformation = bi;
	}
	Expression address;

	public Expression getAddress() {
		return address;
	}

	@Override
	public Expression getValue() {
		throw new AssertionError("HeapLValues must be converted to RValue before their value can be queried.");
	}

	public BitfieldInformation getBitfieldInformation() {
		return mBitfieldInformation;
	}

	public RValue getAddressAsPointerRValue(final BoogieType pointerType) {
		return new RValue(address, new CPointer(getCType()));
	}

	public LRValue getAddressAsPointerRValue(final Dispatcher main) {
		return getAddressAsPointerRValue(main.mTypeHandler.getBoogiePointerType());
	}


}
