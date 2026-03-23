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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Stream;

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
	 *
	 * <p>
	 * C11 6.7.2.1.13 allows a struct/union member to have no declarator and no tag, in which case its own members are
	 * promoted into the enclosing struct/union's namespace. Those are represented by {@link AnonymousMember}.
	 */
	public sealed interface Member permits NamedMember, AnonymousMember {
		/** The C type of this member. */
		ICType type();

		int bitFieldWidth();

		List<NamedMember> flatten();
	}

	/**
	 * A regular, named struct/union field, optionally with a bitfield width.
	 *
	 * @param name
	 *            field name; never {@code null} or empty.
	 * @param type
	 *            field type; never {@code null}.
	 * @param bitfieldWidth
	 *            number of bits if this is a bitfield, otherwise {@code -1}.
	 */
	public record NamedMember(String name, ICType type, int bitFieldWidth) implements Member {
		public NamedMember {
			Objects.requireNonNull(name);
			Objects.requireNonNull(type);
			if (name.isEmpty()) {
				throw new IllegalArgumentException("NamedMember name must not be empty");
			}
		}

		/** Convenience constructor for non-bitfield members. */
		public NamedMember(final String name, final ICType type) {
			this(name, type, -1);
		}

		@Override
		public List<NamedMember> flatten() {
			return List.of(this);
		}
	}

	/**
	 * An anonymous nested struct or union member (no declarator, no tag). Its own members are merged into the enclosing
	 * struct/union's namespace at the C level, but we keep the nesting explicit here.
	 *
	 * @param type
	 *            the nested, anonymous {@link CStructOrUnion}
	 */
	public record AnonymousMember(CStructOrUnion type) implements Member {
		@Override
		public int bitFieldWidth() {
			return -1;
		}

		@Override
		public List<NamedMember> flatten() {
			return type.getFlattenedMembers().toList();
		}
	}

	private final StructOrUnion mIsStructOrUnion;

	private List<Member> mMembers;

	private final String mStructName;

	private boolean mIsComplete;

	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name) {
		assert name != null && !name.isEmpty();
		mIsStructOrUnion = isStructOrUnion;
		mMembers = List.of();
		mStructName = Objects.requireNonNull(name);
		mIsComplete = false;
	}

	public CStructOrUnion(final StructOrUnion isStructOrUnion, final String name, final List<Member> members) {
		mIsStructOrUnion = isStructOrUnion;
		mStructName = Objects.requireNonNull(name);
		mMembers = new ArrayList<>(members);
		mIsComplete = true;
	}

	@Override
	public boolean isIncomplete() {
		return !mIsComplete;
	}

	private Optional<Member> lookupMember(final String id) {
		assert !isIncomplete() : "Cannot get a field in an incomplete struct type.";
		for (final Member m : mMembers) {
			switch (m) {
			case final NamedMember named:
				if (named.name().equals(id)) {
					return Optional.of(named);
				}
				break;
			case final AnonymousMember anon:
				final Optional<Member> recLookup = anon.type().lookupMember(id);
				if (recLookup.isPresent()) {
					return recLookup;
				}
				break;
			}
		}
		return Optional.empty();
	}

	/**
	 * Returns the field type, i.e. the type of the field at the given index.
	 *
	 * @param id
	 *            the fields id.
	 * @return the field type.
	 */
	public ICType getFieldType(final String id) {
		final Optional<Member> member = lookupMember(id);
		if (member.isEmpty()) {
			throw new IllegalArgumentException("Field not in struct: " + id);
		}
		return member.get().type();
	}

	/**
	 * Getter for all field types, ordered according to occurence in C code!
	 *
	 * @return the types of this strut's fields.
	 */
	public ICType[] getFieldTypes() {
		return getFlattenedMembers().map(NamedMember::type).toArray(ICType[]::new);
	}

	private Stream<NamedMember> getFlattenedMembers() {
		return mMembers.stream().flatMap(CStructOrUnion::flatten);
	}

	private static Stream<NamedMember> flatten(final Member member) {
		switch (member) {
		case final NamedMember nm:
			return Stream.of(nm);
		case final AnonymousMember am:
			return am.type().getFlattenedMembers();
		}
	}

	public List<Member> getMembers() {
		return Collections.unmodifiableList(mMembers);
	}

	public Member getMember(final int index) {
		return mMembers.get(index);
	}

	/**
	 * Returns the set of fields in this struct.
	 *
	 * @return the set of fields in this struct.
	 */
	public String[] getFieldIds() {
		return getFlattenedMembers().map(NamedMember::name).toArray(String[]::new);
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
		for (final Member m : mMembers) {
			sb.append("?");
			sb.append(m instanceof final NamedMember nm ? nm.name() : "ANON");
			sb.append("~");
			sb.append(m.type());
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
	 * Complete {@code this} in with the given names, types and bitfield widths (in-place).
	 *
	 * @param memberNames
	 *            names of the members to be completed.
	 * @param memberTypes
	 *            types of the members to be completed.
	 * @param bitfieldWidths
	 *            the widths of the bitfields to be completed.
	 */
	public void complete(final List<Member> members) {
		mMembers = new ArrayList<>(members);
		mIsComplete = true;
	}

	/**
	 * If field with name id is a bitfield returns the bit width (i.e., number of bits of the bitfield) otherwise
	 * returns -1.
	 */
	public int getBitfieldWidth(final String id) {
		final Optional<Member> member = lookupMember(id);
		if (member.isEmpty()) {
			throw new IllegalArgumentException("Field not in struct: " + id);
		}
		return member.get().bitFieldWidth();
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
