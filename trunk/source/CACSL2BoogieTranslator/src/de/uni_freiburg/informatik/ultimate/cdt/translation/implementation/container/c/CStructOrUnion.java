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

/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 */
public class CStructOrUnion extends CType implements ICPossibleIncompleteType<CStructOrUnion> {

	public enum StructOrUnion {
		STRUCT, UNION,
	}

	private final StructOrUnion mIsStructOrUnion;
	/**
	 * Field names.
	 */
	private String[] mFieldNames;
	/**
	 * Field types.
	 */
	private CType[] mFieldTypes;

	/**
	 * Indicates if this represents an incomplete type. If 'this' is complete, this String is empty, otherwise it holds
	 * the name of the incomplete struct.
	 */
	private final String mStructName;

	private List<Integer> mBitFieldWidths;

	private boolean mIsComplete;

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
	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name, final String[] fNames,
			final CType[] fTypes, final List<Integer> bitFieldWidths) {
		// FIXME: integrate those flags -- you will also need to change the equals method if you do
		super(false, false, false, false, false);
		assert name != null;
		mIsStructOrUnion = isStructOrUnion;
		mFieldNames = fNames;
		mFieldTypes = fTypes;
		mBitFieldWidths = Collections.unmodifiableList(bitFieldWidths);
		mStructName = name;
		mIsComplete = true;
	}

	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name) {
		// FIXME: integrate those flags -- you will also need to change the equals method if you do
		super(false, false, false, false, false);
		assert name != null && !name.isEmpty();
		mIsStructOrUnion = isStructOrUnion;
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

	public StructOrUnion isStructOrUnion() {
		return mIsStructOrUnion;
	}

	@Override
	public String toString() {
		final String structOrUnionPrefix = getPrefix(mIsStructOrUnion);

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

	@Override
	public CStructOrUnion complete(final CStructOrUnion cvar) {
		if (!isIncomplete()) {
			throw new AssertionError("only incomplete structs can be completed");
		}
		return new CStructOrUnion(cvar.isStructOrUnion(), mStructName, cvar.mFieldNames, cvar.mFieldTypes,
				cvar.getBitFieldWidths());
	}

	public void complete(final String[] memberNames, final CType[] memberTypes, final List<Integer> bitfieldWidth) {
		mFieldNames = memberNames;
		mFieldTypes = memberTypes;
		mBitFieldWidths = bitfieldWidth;
		mIsComplete = true;
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
		if (!(oType instanceof CStructOrUnion)) {
			return false;
		}

		final CStructOrUnion oStruct = (CStructOrUnion) oType;
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

	public static boolean isUnion(final CType cType) {
		if (cType instanceof CStructOrUnion) {
			return ((CStructOrUnion) cType).isStructOrUnion() == StructOrUnion.UNION;
		}
		return false;
	}

	@Override
	public int hashCode() {
		// reproducible hash codes, but object equality
		return mStructName.hashCode();
//		final int prime = 31;
//		int result = super.hashCode();
//		result = prime * result + ((mBitFieldWidths == null) ? 0 : mBitFieldWidths.hashCode());
//		result = prime * result + Arrays.hashCode(mFieldNames);
//		result = prime * result + Arrays.hashCode(mFieldTypes);
//		result = prime * result + (mIsComplete ? 1231 : 1237);
//		result = prime * result + ((mIsStructOrUnion == null) ? 0 : mIsStructOrUnion.hashCode());
//		result = prime * result + ((mStructName == null) ? 0 : mStructName.hashCode());
//		return result;
	}

//	@Override
//	public boolean equals(final Object o) {
//		if (o == null) {
//			return false;
//		}
//		if (o == this) {
//			return true;
//		}
//		if (!(o instanceof CType)) {
//			return false;
//		}
//		final CType oType = ((CType) o).getUnderlyingType();
//		if (!(oType instanceof CStructOrUnion)) {
//			return false;
//		}
//
//		final CStructOrUnion oStruct = (CStructOrUnion) oType;
//		if (mIsStructOrUnion != oStruct.isStructOrUnion()) {
//			return false;
//		}
//		if (mFieldNames.length != oStruct.mFieldNames.length) {
//			return false;
//		}
//		for (int i = mFieldNames.length - 1; i >= 0; --i) {
//			if (!(mFieldNames[i].equals(oStruct.mFieldNames[i]))) {
//				return false;
//			}
//		}
//		if (mFieldTypes.length != oStruct.mFieldTypes.length) {
//			return false;
//		}
//		for (int i = mFieldTypes.length - 1; i >= 0; --i) {
//			if (!(mFieldTypes[i].equals(oStruct.mFieldTypes[i]))) {
//				return false;
//			}
//		}
//		return true;
//	}


	public static String getPrefix(final StructOrUnion structOrUnion) {
		switch (structOrUnion) {
		case STRUCT:
			return "STRUCT~";
		case UNION:
			return "UNION~";
		default:
			throw new AssertionError();
		}
	}

}
