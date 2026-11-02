/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2025-2026 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2026 University of Freiburg
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

import java.util.List;
import java.util.Objects;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

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

	/**
	 * A single member of a struct or union. A member is either a named field ({@link NamedMember}) or an anonymous
	 * nested struct/union ({@link AnonymousMember}).
	 */
	public sealed interface Member permits NamedMember, AnonymousMember {
		ICType type();

		int bitfieldWidth();
	}

	/**
	 * A regular member with a name and an optional bitfield width
	 */
	public record NamedMember(String name, ICType type, int bitfieldWidth) implements Member {
		public NamedMember {
			Objects.requireNonNull(name);
			Objects.requireNonNull(type);
		}

		public NamedMember(final String name, final ICType type) {
			this(name, type, -1);
		}
	}

	/**
	 * An anonymous struct / union member (see C11 6.7.2.1.13). The members of its type are accessible as if they were
	 * members of the surrounding type.
	 */
	public record AnonymousMember(CStructOrUnion type) implements Member {
		public AnonymousMember {
			Objects.requireNonNull(type);
		}

		@Override
		public int bitfieldWidth() {
			return -1;
		}
	}

	private final StructOrUnion mIsStructOrUnion;

	private final String mStructName;

	private List<Member> mMembers;

	private boolean mIsComplete;

	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name, final List<Member> members) {
		mIsStructOrUnion = isStructOrUnion;
		mMembers = members;
		mStructName = Objects.requireNonNull(name);
		mIsComplete = true;
	}

	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name) {
		assert name != null && !name.isEmpty();
		mIsStructOrUnion = isStructOrUnion;
		mMembers = List.of();
		mStructName = Objects.requireNonNull(name);
		mIsComplete = false;
	}

	@Override
	public boolean isIncomplete() {
		return !mIsComplete;
	}

	/**
	 * Get the number of fields in this struct. Anonymous fields are also considered.
	 *
	 * @return the number of fields.
	 */
	public int getFieldCount() {
		return mMembers.size();
	}

	/**
	 * Returns the field type, i.e. the type of the field at the given index. Anonymous fields are looked up
	 * recursively.
	 *
	 * @param id
	 *            the fields id.
	 * @return the field type.
	 */
	public ICType getFieldType(final String id) {
		return lookupField(id).member().type();
	}

	/**
	 * Getter for all field types, ordered according to occurence in C code!
	 *
	 * @return the types of this struct's fields.
	 */
	public ICType[] getFieldTypes() {
		return mMembers.stream().map(Member::type).toArray(ICType[]::new);
	}

	/**
	 * Returns the set of fields in this struct.
	 *
	 * @return the set of fields in this struct.
	 */
	public String[] getFieldIds() {
		return IntStream.range(0, mMembers.size()).mapToObj(this::getFieldId).toArray(String[]::new);
	}

	/**
	 * Returns the name of the member at the given position. Anonymous members get a generated name that is unique
	 * within this type.
	 */
	private String getFieldId(final int index) {
		if (mMembers.get(index) instanceof final NamedMember named) {
			return named.name();
		}
		return "#anon~" + index;
	}

	@Override
	public String getName() {
		return mStructName;
	}

	public StructOrUnion isStructOrUnion() {
		return mIsStructOrUnion;
	}

	/**
	 * Result of a recursive field lookup.
	 *
	 * @param path
	 *            the path of field names that leads to the member.
	 * @param member
	 *            the member that was found.
	 */
	private record FieldLookup(List<String> path, Member member) {
	}

	private FieldLookup lookupFieldRecursive(final String id) {
		assert !isIncomplete() : "Cannot check field in an incomplete struct type.";
		// Anonymous member IDs are only unique within their owning struct. Resolve a local ID before searching
		// fields of anonymous members, where the same generated ID may occur in a nested type.
		for (int i = 0; i < mMembers.size(); i++) {
			if (id.equals(getFieldId(i))) {
				return new FieldLookup(List.of(id), mMembers.get(i));
			}
		}
		for (int i = 0; i < mMembers.size(); i++) {
			final Member member = mMembers.get(i);
			if (member instanceof final AnonymousMember anon) {
				final FieldLookup nestedResult = anon.type().lookupFieldRecursive(id);
				if (nestedResult != null) {
					return new FieldLookup(DataStructureUtils.concat(List.of(getFieldId(i)), nestedResult.path()),
							nestedResult.member());
				}
			}
		}
		return null;
	}

	public boolean hasField(final String id) {
		return lookupFieldRecursive(id) != null;
	}

	private FieldLookup lookupField(final String id) {
		final FieldLookup result = lookupFieldRecursive(id);
		if (result == null) {
			throw new IllegalArgumentException("Field not in struct: " + id);
		}
		return result;
	}

	/**
	 * Returns the path of field names through anonymous members that leads to the member with the given name.
	 */
	public List<String> getFieldPath(final String id) {
		return lookupField(id).path();
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
			sb.append(getFieldId(i));
			sb.append("~");
			sb.append(mMembers.get(i).type().toString());
		}
		sb.append("#");
		return sb.toString();
	}

	@Override
	public CStructOrUnion complete(final CStructOrUnion cvar) {
		if (!isIncomplete()) {
			throw new AssertionError("only incomplete structs can be completed");
		}
		return new CStructOrUnion(cvar.isStructOrUnion(), mStructName, cvar.mMembers);
	}

	/**
	 * Complete {@code this} with the given members (in-place).
	 */
	public void complete(final List<Member> members) {
		mMembers = List.copyOf(members);
		mIsComplete = true;
	}

	public List<Integer> getBitFieldWidths() {
		return mMembers.stream().map(Member::bitfieldWidth).toList();
	}

	/**
	 * If field with name id is a bitfield returns the bit width (i.e., number of bits of the bitfield) otherwise
	 * returns -1. Anonymous fields are looked up recursively.
	 */
	public int getBitfieldWidth(final String id) {
		return lookupField(id).member().bitfieldWidth();
	}

	public static boolean isUnion(final ICType cType) {
		if (cType instanceof final CStructOrUnion cStructOrUnion) {
			return cStructOrUnion.isStructOrUnion() == StructOrUnion.UNION;
		}
		return false;
	}

	public boolean hasFlexibleArrayMember() {
		if (mMembers.isEmpty()) {
			return false;
		}
		final ICType lastMember = mMembers.getLast().type();
		return lastMember instanceof CArray && lastMember.isIncomplete();
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

	public static String getPrefix(final StructOrUnion structOrUnion) {
		return switch (structOrUnion) {
		case STRUCT -> "STRUCT~";
		case UNION -> "UNION~";
		};
	}

	@Override
	public boolean isAtomic() {
		return false;
	}
}
