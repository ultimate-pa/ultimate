/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import java.util.Arrays;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;

/**
 * Enum types (see C11 6.2.5.16)
 *
 * @author Markus Lindenmann
 * @author nutz
 * @date 18.09.2012
 */
public final class CEnum implements ICType, ICPossibleIncompleteType<CEnum> {
	/**
	 * Field names.
	 */
	private final String[] mNames;
	/**
	 * The _boogie_ identifier of this enum set.
	 */
	private final String mIdentifier;

	private final boolean mIsComplete;

	/**
	 * The integer type this enumerated type is compatible with (C11 6.7.2.2.4), i.e., the type in which we represent
	 * values of this enumerated type.
	 */
	private final CPrimitive mIntegerType;

	/**
	 * Constructor.
	 *
	 * @param id
	 *            this enums identifier.
	 * @param fNames
	 *            field names.
	 * @param integerType
	 *            the integer type this enumerated type is compatible with
	 */
	public CEnum(final String id, final String[] fNames, final CPrimitive integerType) {
		assert id != null;
		assert integerType.getGeneralType() == CPrimitiveCategory.INTTYPE;
		mIdentifier = id;
		mNames = fNames;
		mIsComplete = true;
		mIntegerType = integerType;
	}

	/**
	 * Constructor for an incomplete enumerated type. Until it is completed, we use int as its integer type.
	 */
	public CEnum(final String id) {
		mIdentifier = id;
		mIsComplete = false;
		mNames = null;
		mIntegerType = new CPrimitive(CPrimitives.INT);
	}

	/**
	 * Get the number of fields in this enum.
	 *
	 * @return the number of fields.
	 */
	public int getFieldCount() {
		if (mNames == null) {
			return 0;
		}
		return mNames.length;
	}

	/**
	 * Returns the set of fields in this enum.
	 *
	 * @return the set of fields in this enum.
	 */
	public String[] getFieldIds() {
		return mNames;
	}

	/**
	 * Getter for this enums identifier.
	 *
	 * @return this enums identifier.
	 */
	@Override
	public String getName() {
		return mIdentifier;
	}

	@Override
	public String toString() {
		return mIdentifier;
	}

	@Override
	public boolean isIncomplete() {
		return !mIsComplete;
	}

	@Override
	public CEnum complete(final CEnum cEnum) {
		return new CEnum(getName(), cEnum.getFieldIds(), cEnum.getIntegerType());
	}

	/**
	 * @return the integer type this enumerated type is compatible with (C11 6.7.2.2.4)
	 */
	public CPrimitive getIntegerType() {
		return mIntegerType;
	}

	/**
	 * Replace a CEnum type by the integer type it is compatible with, other types are untouched.
	 *
	 * @param cType
	 *            a given C-type
	 * @return either cType itself or the integer type of the enum
	 */
	public static ICType replaceEnumWithIntegerType(final ICType cType) {
		if (cType.getUnderlyingType() instanceof final CEnum cEnum) {
			return cEnum.getIntegerType();
		}
		return cType;
	}

	@Override
	public int hashCode() {
		return Objects.hash(mIdentifier, mIsComplete, Arrays.hashCode(mNames), mIntegerType);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final CEnum other = (CEnum) obj;
		return Objects.equals(mIdentifier, other.mIdentifier) && mIsComplete == other.mIsComplete
				&& Arrays.equals(mNames, other.mNames) && Objects.equals(mIntegerType, other.mIntegerType);
	}

	@Override
	public boolean isAtomic() {
		return false;
	}

	@Override
	public ICType toAtomic() {
		throw new UnsupportedOperationException("Atomic enums are not supported yet.");
	}

	@Override
	public boolean isIntegerType() {
		return true;
	}
}
