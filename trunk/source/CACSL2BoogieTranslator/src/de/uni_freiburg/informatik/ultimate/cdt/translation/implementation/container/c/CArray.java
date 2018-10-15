/*
 * Copyright (C) 2013-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
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
/**
 * Describes an array given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class CArray extends CType {

	/**
	 * Size that we use to indicate that an array has a variable length.
	 */
	public static final int INCOMPLETE_ARRY_MAGIC_NUMBER = -1234567;

	/**
	 * Array bound. Note that we use nesting of array types for multidimensional array types
	 */
	private final RValue mBound;

	private final CType mValueType;

	/**
	 * Constructor.
	 *
	 * @param dimensions
	 *            the dimensions of this array.
	 * @param valueType
	 *            the type of the array.
	 * @param cDeclSpec
	 *            the C declaration used.
	 */
	public CArray(final RValue bound, final CType valueType) {
		// FIXME: integrate those flags
		super(false, false, false, false, false);
		mBound = bound;
		mValueType = valueType;
	}

	/**
	 * @return the dimensions
	 */
	public RValue getBound() {
		return mBound;
	}

	/**
	 * @return the valueType
	 */
	public CType getValueType() {
		return mValueType;
	}

	@Override
	public String toString() {
		final StringBuilder id = new StringBuilder("ARRAY#");
		final StringBuilder dimString = new StringBuilder("_");

		final Expression dim = mBound.getValue();
		if (dim instanceof BinaryExpression || dim instanceof UnaryExpression) {
			// 2015-11-08 Matthias: Use C representation or introduce a factory
			// for types.
			dimString.append(dim.toString());
			// dim = getArithmeticResultAsIntegerLiteral(dim);
		}
		if (dim instanceof IntegerLiteral) {
			dimString.append(((IntegerLiteral) dim).getValue());
			dimString.append("_");
		} else if (dim instanceof IdentifierExpression) {
			dimString.append(((IdentifierExpression) dim).getIdentifier());
			dimString.append("_");
		} else {
			dimString.append("unrecognizedDimensions");
			dimString.append("_");
		}

		id.append(dimString.toString());
		id.append("~");
		id.append(mValueType.toString());
		id.append("#");
		return id.toString();
	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof CType)) {
			return false;
		}
		final CType oType = ((CType) o).getUnderlyingType();
		if (!(oType instanceof CArray)) {
			return false;
		}

		final CArray oArr = (CArray) oType;
		if (!(mValueType.equals(oArr.mValueType))) {
			return false;
		}
		if (!(mBound.equals(oArr.mBound))) {
			return false;
		}

		return true;
	}

	@Override
	public boolean isCompatibleWith(final CType o) {
		if (o instanceof CPrimitive && ((CPrimitive) o).getType() == CPrimitives.VOID) {
			return true;
		}

		final CType oType = o.getUnderlyingType();
		if (!(oType instanceof CArray)) {
			return false;
		}

		final CArray oArr = (CArray) oType;
		if (!(mValueType.isCompatibleWith(oArr.mValueType))) {
			return false;
		}
		if (!(mBound.equals(oArr.mBound))) {
			return false;
		}

		return true;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashJenkins(31, mBound, mValueType);
	}

	@Override
	public boolean isIncomplete() {
		final BigInteger boundValue = CTranslationUtil.extractIntegerValue(mBound.getValue());
		if (boundValue == null) {
			return true;
		} else {
			return BigInteger.valueOf(INCOMPLETE_ARRY_MAGIC_NUMBER).equals(boundValue);
		}
	}
}
