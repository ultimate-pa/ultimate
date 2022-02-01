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
 * An option specialized to BigIntegers.  This option is currently unused.
 * @author Juergen Christ
 */
public class BigIntegerOption extends Option {

	private BigInteger mValue;
	private BigInteger mDefaultValue;

	public BigIntegerOption(BigInteger defaultValue, boolean onlineModifiable,
			String description) {
		super(onlineModifiable, description);
		mValue = mDefaultValue = defaultValue;
	}

	BigIntegerOption(BigIntegerOption other) {
		super(other.isOnlineModifiable(), other.getDescription());
		mValue = other.mValue;
		mDefaultValue = other.mDefaultValue;
	}

	@Override
	public Option copy() {
		return new BigIntegerOption(this);
	}

	@Override
	public void set(Object value) {
		if (value instanceof BigInteger) {
			mValue = (BigInteger) value;
		} else if (value instanceof String) {
			try {
				mValue = new BigInteger((String) value);
			} catch (final NumberFormatException enfe) {
				throw new SMTLIBException(enfe.getMessage());
			}
		} else {
			throw new SMTLIBException("Not a number: " + value);
		}
	}

	public final BigInteger getValue() {
		return mValue;
	}

	@Override
	public Object get() {
		return mValue;
	}

	@Override
	public void reset() {
		mValue = mDefaultValue;
	}

	@Override
	public Object defaultValue() {
		return mDefaultValue;
	}

	@Override
	public void started() {
		mDefaultValue = mValue;
	}

}
