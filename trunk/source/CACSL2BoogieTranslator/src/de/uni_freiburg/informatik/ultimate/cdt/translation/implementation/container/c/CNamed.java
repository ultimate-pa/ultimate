/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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

import java.util.Objects;

/**
 * Describes a named type given in C.
 *
 * @author Markus Lindenmann
 * @date 01.11.2012
 */
public final class CNamed implements ICType {
	/**
	 * The type this named type is mapping to.
	 */
	private final ICType mMappedType;

	/**
	 * The name that is mapped.
	 *
	 * This is the unique name used in the translated Boogie code; not the original C name.
	 */
	private final String mName;

	/**
	 * Constructor.
	 *
	 * @param name
	 *            the unique name used in the translated Boogie code
	 * @param mappedType
	 *            the type this named type is referring to.
	 */
	public CNamed(final String name, final ICType mappedType) {
		mName = name;
		mMappedType = mappedType;
	}

	/**
	 * Getter for the named declaration's name.
	 *
	 * @return the named declaration's unique name used in the translated Boogie code.
	 */
	public String getName() {
		return mName;
	}

	/**
	 * Getter for the real underlying type.
	 *
	 * @return the type this named type is referring to.
	 */
	@Override
	public ICType getUnderlyingType() {
		return mMappedType.getUnderlyingType();
	}

	@Override
	public String toString() {
		return getName();
	}

	@Override
	public boolean isIncomplete() {
		return getUnderlyingType().isIncomplete();
	}

	@Override
	public int hashCode() {
		return Objects.hash(mMappedType, mName);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final CNamed other = (CNamed) obj;
		return Objects.equals(mMappedType, other.mMappedType) && Objects.equals(mName, other.mName);
	}

	@Override
	public boolean isAtomic() {
		return mMappedType.isAtomic();
	}

	@Override
	public boolean isVoidPointerType() {
		return mMappedType.isVoidPointerType();
	}

	@Override
	public boolean isVoidType() {
		return mMappedType.isVoidType();
	}
}
