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

import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;

/**
 *
 * @author Alexander Nutz, Matthias Heizmann
 *
 */
public abstract class LRValue {

	private final CType mCType;

	/**
	 * This flag is supposed to be true iff the value-expression of this LRValue is of boolean type in boogie. For
	 * instance if it is the translation of a comparator expression like x == 0.
	 */
	private final boolean mIsBoogieBool;

	private final boolean mIsIntFromPointer;

	/**
	 * Abstract class constructor -- all inheritors of LRValue have at least an expression representing what the
	 * containing result evaluates to.
	 *
	 * @param mValue
	 */
	public LRValue(final CType cType, final boolean isBoogieBool, final boolean isIntFromPointer) {
		mCType = cType;
		mIsBoogieBool = isBoogieBool;
		mIsIntFromPointer = isIntFromPointer;
	}

	public abstract Expression getValue();

	public CType getCType() {
		return mCType;
	}

	public CType getUnderlyingType() {
		return mCType.getUnderlyingType();
	}

	public boolean isBoogieBool() {
		return mIsBoogieBool;
	}

	public boolean isIntFromPointer() {
		return mIsIntFromPointer;
	}

	@Override
	public final String toString() {
		if (this instanceof HeapLValue) {
			return "address: " + ((HeapLValue) this).getAddress();
		} else if (this instanceof LocalLValue) {
			return "lhs: " + ((LocalLValue) this).getLhs();
		} else {
			return "value: " + getValue();
		}
	}

	/**
	 * Returns true iff this LRValue is a null pointer constant according to the definition 6.3.2.3.3 in the C11
	 * standard.
	 * <p>
	 * C11 6.3.2.3.3 An integer constant expression with the value 0, or such an expression cast to type void *, is
	 * called a null pointer constant. footnote: The macro NULL is defined in <stddef.h> (and other headers) as a null
	 * pointer constant; see 7.19.
	 */
	public boolean isNullPointerConstant() {
		if (!getCType().isVoidPointerType() && !getCType().isArithmeticType()) {
			return false;
		}

		final Expression value;
		if (this instanceof HeapLValue) {
			value = ((HeapLValue) this).getAddress();
			throw new AssertionError("unexpected: double check this case");
		}
		value = getValue();

		if (value instanceof IntegerLiteral) {
			return "0".equals(((IntegerLiteral) value).getValue());
		}
		if (value instanceof BitvecLiteral) {
			return "0".equals(((BitvecLiteral) value).getValue());
		}
		if (value instanceof IdentifierExpression) {
			return SFO.NULL.equals(((IdentifierExpression) value).getIdentifier());
		}
		return false;
	}
}
