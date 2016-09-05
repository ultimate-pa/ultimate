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

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;

/**
 * Option specialized for long values.  The interface methods return a
 * BigInteger to be backward compatible.
 * @author Juergen Christ
 */
public class LongOption extends Option {

	private long mValue;
	private long mDefaultValue;

	public LongOption(long defaultValue, boolean onlineModifiable,
			String description) {
		super(onlineModifiable, description);
		mValue = mDefaultValue = defaultValue;
	}
	
	LongOption(LongOption other) {
		super(other.isOnlineModifiable(), other.getDescription());
		mValue = other.mValue;
		mDefaultValue = other.mDefaultValue;
	}
	@Override
	public Option copy() {
		return new LongOption(this);
	}

	@Override
	public void set(Object value) {
		if (value instanceof Number) {
			mValue = ((Number) value).longValue();
		} else if (value instanceof String) {
			try {
				mValue = Long.parseLong((String) value);
			} catch (final NumberFormatException enfe) {
				throw new SMTLIBException(enfe.getMessage());
			}
		} else {
			throw new SMTLIBException("Not a number: " + value);
		}
	}
	
	public final long getValue() {
		return mValue;
	}

	@Override
	public Object get() {
		return BigInteger.valueOf(mValue);
	}

	@Override
	public void reset() {
		mValue = mDefaultValue;
	}

	@Override
	public Object defaultValue() {
		return BigInteger.valueOf(mDefaultValue);
	}

	@Override
	public void started() {
		mDefaultValue = mValue;
	}

}
