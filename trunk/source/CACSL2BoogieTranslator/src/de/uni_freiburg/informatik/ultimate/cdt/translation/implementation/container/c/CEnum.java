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
/**
 * Describes an enum given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * @author Markus Lindenmann
 * @author nutz
 * @date 18.09.2012
 */
public class CEnum extends CType {
	/**
	 * Field names.
	 */
	private String[] mNames;
	/**
	 * Field values.
	 */
	private Expression[] mValues;
	/**
	 * The _boogie_ identifier of this enum set.
	 */
	private final String mIdentifier;

	/**
	 * Constructor.
	 *
	 * @param fNames
	 *            field names.
	 * @param fValues
	 *            field values.
	 * @param cDeclSpec
	 *            the C declaration used.
	 * @param id
	 *            this enums identifier.
	 */
	public CEnum(final String id, final String[] fNames, final Expression[] fValues) {
		super(false, false, false, false); // FIXME: integrate those flags
		assert fNames.length == fValues.length;
		mIdentifier = id;
		mNames = fNames;
		mValues = fValues;
	}

	public CEnum(final String id) {
		super(false, false, false, false); // FIXME: integrate those flags
		mIdentifier = id;
		mNames = null;
		mValues = null;
	}

	/**
	 * Get the number of fields in this enum.
	 *
	 * @return the number of fields.
	 */
	public int getFieldCount() {
		return mNames.length;
	}

	/**
	 * Returns the field value.
	 *
	 * @param id
	 *            the fields id.
	 * @return the fields value.
	 */
	public Expression getFieldValue(final String id) {
		final int idx = Arrays.asList(mNames).indexOf(id);
		if (idx < 0) {
			throw new IllegalArgumentException("Field '" + id + "' not in struct!");
		}
		return mValues[idx];
	}

	/**
	 * Returns the set of fields in this enum.
	 *
	 * @return the set of fields in this enum.
	 */
	public String[] getFieldIds() {
		return mNames.clone();
	}

	/**
	 * Getter for this enums identifier.
	 *
	 * @return this enums identifier.
	 */
	public String getIdentifier() {
		return mIdentifier;
	}

	@Override
	public String toString() {
		// StringBuilder id = new StringBuilder("ENUM#");
		// for (int i = 0; i < getFieldCount(); i++) {
		// id.append("?");
		// id.append(fNames[i]);
		// }
		// id.append("#");
		// return id.toString();
		return mIdentifier;
	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof CType)) {
			return false;
		}
		final CType oType = ((CType) o).getUnderlyingType();
		if (!(oType instanceof CEnum)) {
			return false;
		}

		final CEnum oEnum = (CEnum) oType;
		if (!(mIdentifier.equals(oEnum.mIdentifier))) {
			return false;
		}
		if (mNames.length != oEnum.mNames.length) {
			return false;
		}
		for (int i = mNames.length - 1; i >= 0; --i) {
			if (!(mNames[i].equals(oEnum.mNames[i]))) {
				return false;
			}
		}
		return true;
	}

	// @Override
	@Override
	public boolean isIncomplete() {
		return mNames == null;
	}

	public void complete(final CEnum cEnum) {
		mNames = cEnum.mNames;
		mValues = cEnum.mValues;

	}

	@Override
	public boolean isCompatibleWith(final CType o) {
		if (o instanceof CPrimitive && (((CPrimitive) o).getType() == CPrimitives.VOID
				|| ((CPrimitive) o).getGeneralType() == CPrimitiveCategory.INTTYPE)) {
			return true;
		}

		final CType oType = o.getUnderlyingType();
		if (!(oType instanceof CEnum)) {
			return false;
		}

		final CEnum oEnum = (CEnum) oType;
		if (!(mIdentifier.equals(oEnum.mIdentifier))) {
			return false;
		}
		if (mNames.length != oEnum.mNames.length) {
			return false;
		}
		for (int i = mNames.length - 1; i >= 0; --i) {
			if (!(mNames[i].equals(oEnum.mNames[i]))) {
				return false;
			}
		}
		return true;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashJenkins(31, mNames, mValues, mIdentifier);
	}

	/**
	 * Replace CEnum types by signed int, other types are untouched. According to C11 6.4.4.3.2 an identifier declared
	 * as an enumeration constant has type int.
	 *
	 */
	public static CType replaceEnumWithInt(final CType cType) {
		if (cType.getUnderlyingType() instanceof CEnum) {
			return new CPrimitive(CPrimitives.INT);
		}
		return cType;
	}
}
