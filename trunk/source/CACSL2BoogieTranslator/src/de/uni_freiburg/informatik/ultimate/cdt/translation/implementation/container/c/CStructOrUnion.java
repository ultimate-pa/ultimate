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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;

/**
 * Struct / Union type (see C11 6.2.5.20.2/3)
 *
 * @author Markus Lindenmann
 * @date 18.09.2012
 */
public final class CStructOrUnion implements ICType, ICPossibleIncompleteType<CStructOrUnion> {

	public enum StructOrUnion {
		STRUCT, UNION,
	}

	private final StructOrUnion mIsStructOrUnion;

	private final boolean mIsAnonymous;

	/**
	 * Field names.
	 */
	private String[] mFieldNames;
	/**
	 * Field types.
	 */
	private ICType[] mFieldTypes;

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
	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name, final List<String> fNames,
			final List<ICType> fTypes, final List<Integer> bitFieldWidths) {
		this(isStructOrUnion, name, fNames.toArray(String[]::new), fTypes.toArray(ICType[]::new), bitFieldWidths);
	}

	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name, final String[] fNames,
			final ICType[] fTypes, final List<Integer> bitFieldWidths) {
		assert name != null;
		assert fNames.length == bitFieldWidths.size();
		mIsStructOrUnion = isStructOrUnion;
		mIsAnonymous = name.isEmpty() ? true : false;
		mFieldNames = fNames;
		mFieldTypes = fTypes;
		mBitFieldWidths = Collections.unmodifiableList(bitFieldWidths);
		mStructName = isAnonymous() ? Objects.requireNonNull(name) : new String();
		mIsComplete = true;
	}

	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name) {
		assert name != null;
		mIsStructOrUnion = isStructOrUnion;
		mIsAnonymous = name.isEmpty() ? true : false;
		mFieldNames = new String[0];
		mFieldTypes = new ICType[0];
		mBitFieldWidths = Collections.emptyList();
		mStructName = isAnonymous() ? Objects.requireNonNull(name) : new String();
		mIsComplete = false;
	}

	public CStructOrUnion(final StructOrUnion isStructOrUnion) {
		mIsStructOrUnion = isStructOrUnion;
		mIsAnonymous = true;
		mFieldNames = new String[0];
		mFieldTypes = new ICType[0];
		mBitFieldWidths = Collections.emptyList();
		mStructName = null;
		mIsComplete = false;
	}

	@Override
	public boolean isIncomplete() {
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
	public ICType getFieldType(final String id) {
		assert !isIncomplete() : "Cannot get a field type in an incomplete struct type.";
		final int idx = Arrays.asList(mFieldNames).indexOf(id);
		if (idx < 0) {
			throw new IllegalArgumentException("Field not in struct: " + id);
		}
		return mFieldTypes[idx];
	}

	/**
	 * Getter for all field types, ordered according to occurence in C code!
	 *
	 * @return the types of this strut's fields.
	 */
	public ICType[] getFieldTypes() {
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

	public boolean isAnonymous() {
		return mIsAnonymous;
	}

	@Override
	public String toString() {
		final String structOrUnionPrefix = getPrefix(isStructOrUnion(), isAnonymous());

		if (isIncomplete()) {
			return structOrUnionPrefix + "~incomplete~" + getName();
		}
		final StringBuilder sb = new StringBuilder();
		sb.append(structOrUnionPrefix);
		if (!isAnonymous()) {
			sb.append('~');
			sb.append(getName());
		}
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
		assert cvar.mFieldNames.length == cvar.getBitFieldWidths().size();
		return new CStructOrUnion(cvar.isStructOrUnion(), mStructName, cvar.mFieldNames, cvar.mFieldTypes,
				cvar.getBitFieldWidths());
	}

	/**
	 * Complete {@code this} in with the given names, types and bitfield widths (in-place).
	 *
	 * @param memberNames
	 *            names of the members to be completed.
	 * @param memberTypes
	 *            types of the members to be completed.
	 * @param bitfieldWidths
	 *            the widths of the bitfields to be completed.
	 */
	public void complete(final List<String> memberNames, final List<ICType> memberTypes,
			final List<Integer> bitfieldWidths) {
		assert memberNames.size() == bitfieldWidths.size();
		mFieldNames = memberNames.toArray(String[]::new);
		mFieldTypes = memberTypes.toArray(ICType[]::new);
		mBitFieldWidths = bitfieldWidths;
		mIsComplete = true;
	}

	public List<String> getFieldNames() {
		return Arrays.asList(mFieldNames);
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
		final int idx = getFieldNames().indexOf(id);
		if (idx < 0) {
			throw new IllegalArgumentException("Field not in struct: " + id);
		}
		if (getBitFieldWidths().size() < idx) {
			return -1;
		}
		return getBitFieldWidths().get(idx);
	}

	public static boolean isUnion(final ICType cType) {
		if (cType instanceof final CStructOrUnion cStructOrUnion) {
			return cStructOrUnion.isStructOrUnion() == StructOrUnion.UNION;
		}
		return false;
	}

	@Override
	public int hashCode() {
		// reproducible hash codes, but object equality
		return mStructName.hashCode();
	}

	@Override
	public boolean equals(final Object o) {
		// reproducible hash codes, but object equality
		return this == o;
	}

	public static String getPrefix(final StructOrUnion structOrUnion, final boolean anonymous) {
		final String unnamed = anonymous ? "ANONYMOUS~" : new String();
		return switch (structOrUnion) {
		case STRUCT -> "STRUCT~" + unnamed;
		case UNION -> "UNION~" + unnamed;
		};
	}

	public static StructOrUnion getStructOrUnionFromAstNode(final IASTCompositeTypeSpecifier node) {
		return switch (node.getKey()) {
		case IASTCompositeTypeSpecifier.k_struct -> StructOrUnion.STRUCT;
		case IASTCompositeTypeSpecifier.k_union -> StructOrUnion.UNION;
		default -> throw new UnsupportedOperationException();
		};
	}

	public static boolean isAnonymousFromAstNode(final IASTCompositeTypeSpecifier node) {
		assert node.getKey() == IASTCompositeTypeSpecifier.k_struct
				|| node.getKey() == IASTCompositeTypeSpecifier.k_union;
		return node.getName().toString().isEmpty();
	}

	@Override
	public boolean isAtomic() {
		return false;
	}
}
