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

		/**
		 * @return the width of the bitfield or -1 if the member is not a bitfield.
		 */
		int bitfieldWidth();
	}

	/**
	 * A regular member with a name and an optional bitfield width (-1 if there is none).
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
	public record AnonymousMember(ICType type) implements Member {
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

	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name) {
		assert name != null && !name.isEmpty();
		mIsStructOrUnion = isStructOrUnion;
		mStructName = Objects.requireNonNull(name);
		mMembers = List.of();
		mIsComplete = false;
	}

	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name, final List<Member> members) {
		mIsStructOrUnion = isStructOrUnion;
		mStructName = Objects.requireNonNull(name);
		mMembers = List.copyOf(members);
		mIsComplete = true;
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
		return mMembers.size();
	}

	/**
	 * Returns the field type, i.e. the type of the field with the given id. Members of anonymous members are found
	 * recursively.
	 *
	 * @param id
	 *            the fields id.
	 * @return the field type.
	 */
	public ICType getFieldType(final String id) {
		assert !isIncomplete() : "Cannot get a field type in an incomplete struct type.";
		return getMember(id).type();
	}

	/**
	 * Recursively look up a member. Members of anonymous struct / union members are considered members of this type.
	 *
	 * @return the chain of direct field names that leads to the member, i.e., a single element if the member is a
	 *         direct member and a longer list if it is contained in (nested) anonymous members. Returns {@code null} if
	 *         there is no such member.
	 */
	private List<String> findFieldPath(final String id) {
		if (indexOfField(id) >= 0) {
			return List.of(id);
		}
		for (int i = 0; i < mMembers.size(); i++) {
			switch (mMembers.get(i)) {
			case final NamedMember named:
				if (named.name().equals(id)) {
					return List.of(id);
				}
				break;
			case final AnonymousMember anon:
				if (anon.type().getUnderlyingType() instanceof final CStructOrUnion nested) {
					final List<String> nestedPath = nested.findFieldPath(id);
					if (nestedPath != null) {
						return DataStructureUtils.concat(List.of(getFieldName(i)), nestedPath);
					}
				}
				break;
			}
		}
		return null;
	}

	/**
	 * @return the name of the member at the given position. Anonymous members get a generated name that is unique
	 *         within this type (it contains '#' and hence cannot clash with C identifiers).
	 */
	private String getFieldName(final int index) {
		final Member member = mMembers.get(index);
		if (member instanceof final NamedMember named) {
			return named.name();
		}
		return "#anon~" + index;
	}

	private int indexOfField(final String id) {
		for (int i = 0; i < mMembers.size(); i++) {
			if (getFieldName(i).equals(id)) {
				return i;
			}
		}
		return -1;
	}

	/**
	 * Like {@link #findFieldPath(String)} but throws an {@link IllegalArgumentException} if the member does not exist.
	 */
	public List<String> getFieldPath(final String id) {
		final List<String> path = findFieldPath(id);
		if (path == null) {
			throw new IllegalArgumentException("Field not in struct: " + id);
		}
		return path;
	}

	/**
	 * @return the member with the given name; members of anonymous members are found recursively.
	 */
	private Member getMember(final String id) {
		CStructOrUnion current = this;
		Member result = null;
		for (final String step : getFieldPath(id)) {
			result = current.getDirectMember(step);
			if (result.type().getUnderlyingType() instanceof final CStructOrUnion next) {
				current = next;
			}
		}
		return result;
	}

	private Member getDirectMember(final String id) {
		final int idx = indexOfField(id);
		if (idx < 0) {
			throw new IllegalArgumentException("Field not in struct: " + id);
		}
		return mMembers.get(idx);
	}

	/**
	 * Getter for all field types, ordered according to occurence in C code!
	 *
	 * @return the types of this strut's fields.
	 */
	public ICType[] getFieldTypes() {
		return mMembers.stream().map(Member::type).toArray(ICType[]::new);
	}

	/**
	 * Returns the names of the fields in this struct, ordered according to occurence in C code.
	 *
	 * @return the names of the fields in this struct.
	 */
	public String[] getFieldIds() {
		return IntStream.range(0, mMembers.size()).mapToObj(this::getFieldName).toArray(String[]::new);
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
		for (int i = 0; i < mMembers.size(); i++) {
			sb.append("?");
			sb.append(getFieldName(i));
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

	/**
	 * @return the bitfield widths of all members (-1 for members that are no bitfields), ordered like the members.
	 */
	public List<Integer> getBitFieldWidths() {
		return mMembers.stream().map(Member::bitfieldWidth).toList();
	}

	/**
	 * If field with name id is a bitfield returns the bit width (i.e., number of bits of the bitfield) otherwise
	 * returns -1. Members of anonymous members are found recursively.
	 */
	public int getBitfieldWidth(final String id) {
		assert !isIncomplete() : "Cannot get a field type in an incomplete struct type.";
		return getMember(id).bitfieldWidth();
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
		final ICType lastMember = mMembers.get(mMembers.size() - 1).type();
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
