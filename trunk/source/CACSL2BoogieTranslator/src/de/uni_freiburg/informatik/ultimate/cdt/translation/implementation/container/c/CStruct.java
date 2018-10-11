/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
 * Describes a struct given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 */
public class CStruct extends CType implements ICPossibleIncompleteType<CStruct> {
	/**
	 * Field names.
	 */
	private final String[] mFieldNames;
	/**
	 * Field types.
	 */
	private final CType[] mFieldTypes;

	/**
	 * Indicates if this represents an incomplete type. If 'this' is complete, this String is empty, otherwise it holds
	 * the name of the incomplete struct.
	 */
	private final String mStructName;

	private final List<Integer> mBitFieldWidths;

	private final boolean mIsComplete;

	/**
	 * Constructor.
	 *
	 * @param fNames
	 *            field names.
	 * @param fTypes
	 *            field types.
	 * @param bitFieldWidths
	 * @param cDeclSpec
	 *            the C declaration used.
	 */
	public CStruct(final String name, final String[] fNames, final CType[] fTypes, final List<Integer> bitFieldWidths) {
		// FIXME: integrate those flags
		super(false, false, false, false);
		assert name != null;
		mFieldNames = fNames;
		mFieldTypes = fTypes;
		mBitFieldWidths = Collections.unmodifiableList(bitFieldWidths);
		mStructName = name;
		mIsComplete = true;
	}

	public CStruct(final String name) {
		// FIXME: integrate those flags
		super(false, false, false, false);
		assert name != null && !name.isEmpty();
		mFieldNames = new String[0];
		mFieldTypes = new CType[0];
		mBitFieldWidths = Collections.emptyList();
		mStructName = name;
		mIsComplete = false;
	}

	@Override
	public boolean isIncomplete() {
		// FIXME: struct may also be incomplete
		// if last member is array of unknown size
		return !mIsComplete;
	}

	/**
	 * Get the number of fields in this struct.
	 *
	 * @return the number of fields.
	 */
	public int getFieldCount() {
		return mFieldNames.length;
	}

	/**
	 * Returns the field type, i.e. the type of the field at the given index.
	 *
	 * @param id
	 *            the fields id.
	 * @return the field type.
	 */
	public CType getFieldType(final String id) {
		assert !isIncomplete() : "Cannot get a field type in an incomplete struct type.";
		final int idx = Arrays.asList(mFieldNames).indexOf(id);
		if (idx < 0) {
			throw new IllegalArgumentException("Field '" + id + "' not in struct!");
		}
		return mFieldTypes[idx];
	}

	/**
	 * Getter for all field types, ordered according to occurence in C code!
	 *
	 * @return the types of this strut's fields.
	 */
	public CType[] getFieldTypes() {
		return mFieldTypes;
	}

	/**
	 * Returns the set of fields in this struct.
	 *
	 * @return the set of fields in this struct.
	 */
	public String[] getFieldIds() {
		return mFieldNames.clone();
	}

	@Override
	public String getName() {
		return mStructName;
	}

	@Override
	public String toString() {
		final String structOrUnionPrefix = getPrefix();

		if (isIncomplete()) {
			return structOrUnionPrefix + "~incomplete~" + getName();
		}
		final StringBuilder sb = new StringBuilder();
		sb.append(structOrUnionPrefix);
		sb.append('~');
		sb.append(getName());
		for (int i = 0; i < getFieldCount(); i++) {
			sb.append("?");
			sb.append(mFieldNames[i]);
			sb.append("~");
			sb.append(mFieldTypes[i].toString());
		}
		sb.append("#");
		return sb.toString();
	}

	protected String getPrefix() {
		return "STRUCT#";
	}

	@Override
	public boolean equals(final Object o) {
		if (o == null) {
			return false;
		}
		if (o == this) {
			return true;
		}
		if (!(o instanceof CType)) {
			return false;
		}
		final CType oType = ((CType) o).getUnderlyingType();
		if (!(oType instanceof CStruct)) {
			return false;
		}

		final CStruct oStruct = (CStruct) oType;
		if (mFieldNames.length != oStruct.mFieldNames.length) {
			return false;
		}
		for (int i = mFieldNames.length - 1; i >= 0; --i) {
			if (!(mFieldNames[i].equals(oStruct.mFieldNames[i]))) {
				return false;
			}
		}
		if (mFieldTypes.length != oStruct.mFieldTypes.length) {
			return false;
		}
		for (int i = mFieldTypes.length - 1; i >= 0; --i) {
			if (!(mFieldTypes[i].equals(oStruct.mFieldTypes[i]))) {
				return false;
			}
		}
		return true;
	}

	@Override
	public CStruct complete(final CStruct cvar) {
		if (!isIncomplete()) {
			throw new AssertionError("only incomplete structs can be completed");
		}
		return new CStruct(mStructName, cvar.mFieldNames, cvar.mFieldTypes, cvar.getBitFieldWidths());
	}

	@Override
	public boolean isCompatibleWith(final CType o) {
		if (o == null) {
			return false;
		}
		if (this == o) {
			return true;
		}
		if (o instanceof CPrimitive && ((CPrimitive) o).getType() == CPrimitives.VOID) {
			return true;
		}
		final CType oType = o.getUnderlyingType();
		if (!(oType instanceof CStruct)) {
			return false;
		}

		final CStruct oStruct = (CStruct) oType;
		if (mFieldNames.length != oStruct.mFieldNames.length) {
			return false;
		}
		if (mFieldTypes.length != oStruct.mFieldTypes.length) {
			return false;
		}
		for (int i = mFieldTypes.length - 1; i >= 0; --i) {
			if (!(mFieldTypes[i].equals(oStruct.mFieldTypes[i]))) {
				return false;
			}
		}
		return true;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashJenkins(31, mFieldNames, mFieldTypes, mStructName);
	}

	public List<Integer> getBitFieldWidths() {
		return mBitFieldWidths;
	}

	/**
	 * If field with name id is a bitfield returns the bit width (i.e., number of bits of the bitfield) otherwise
	 * returns -1.
	 */
	public int getBitfieldWidth(final String id) {
		assert !isIncomplete() : "Cannot get a field type in an incomplete struct type.";
		final int idx = Arrays.asList(mFieldNames).indexOf(id);
		if (idx < 0) {
			throw new IllegalArgumentException("Field '" + id + "' not in struct!");
		}
		if (getBitFieldWidths().size() < idx) {
			return -1;
		}
		return getBitFieldWidths().get(idx);
	}

}
