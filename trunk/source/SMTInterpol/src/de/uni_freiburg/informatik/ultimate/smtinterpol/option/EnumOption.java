/*
 * Copyright (C) 2014 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.option;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;

/**
 * Option specialized to enums.  The enum class is stored to ensure proper
 * typing when setting a value from this enum.  This is needed since java
 * generics are broken and don't have the generic argument type present at
 * runtime.
 * 
 * For convenience this implementation tries to find enum constants that are
 * written in the way given by the user or after transforming the value to upper
 * cases.
 * 
 * The interface methods return strings to prevent output of some arbitrary
 * string in case an enum overrides the toString() method.
 * @author Juergen Christ
 */
public class EnumOption<E extends Enum<E>> extends Option {

	private E mValue;
	private E mDefaultValue;
	private final Class<E> mClass;
	
	public EnumOption(E defaultValue, boolean onlineModifiable, Class<E> cls,
			String description) {
		super(onlineModifiable, description);
		mValue = mDefaultValue = defaultValue;
		mClass = cls;
	}
	EnumOption(EnumOption<E> other) {
		super(other.isOnlineModifiable(), other.getDescription());
		mValue = other.mValue;
		mDefaultValue = other.mDefaultValue;
		mClass = other.mClass;
	}
	@Override
	public Option copy() {
		return new EnumOption<E>(this);
	}
	@SuppressWarnings("unchecked")
	@Override
	public void set(Object value) {
		if (value instanceof String) {
			try {
				mValue = Enum.valueOf(mClass, (String) value);
			} catch (final IllegalArgumentException ignored) {
				// For convenience: Java enum constants usually are ALL UPPER
				try {
					mValue = Enum.valueOf(mClass, ((String) value).toUpperCase());
				} catch (final IllegalArgumentException eignored) {
					throwException(value);
				}
			}
		} else if (value.getClass().getSuperclass() == mClass) {
			mValue = (E) value;
		} else {
			throwException(value);
		}
	}
	private final void throwException(Object value) {
		final StringBuilder sb = new StringBuilder(50); // NOCHECKSTYLE
		sb.append("Illegal value: ").append(value);
		sb.append(". Only ");
		String sep = "";
		for (final E val : mClass.getEnumConstants()) {
			sb.append(sep).append(val.name());
			sep = ", ";
		}
		sb.append(" allowed!");
		throw new SMTLIBException(sb.toString());
	}

	public final E getValue() {
		return mValue;
	}
	@Override
	public Object get() {
		return mValue.name();
	}

	@Override
	public void reset() {
		mValue = mDefaultValue;
	}

	@Override
	public Object defaultValue() {
		// Just to be sure the value can actually be used.  If an enum
		// overwrites toString() we would end up with a strange output.
		return mDefaultValue.name();
	}
	@Override
	public void started() {
		mDefaultValue = mValue;
	}

}
