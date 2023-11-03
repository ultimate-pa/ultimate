/*
 * Copyright (C) 2020 Leonard Fichtner
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
 * Option specialized for double values.
 *
 * @author LeonardFichtner
 *
 */
public class DoubleOption extends Option {

	double mValue;
	double mDefaultValue;

	public DoubleOption(final double defaultValue, final boolean onlineModifiable, final String description) {
		super(onlineModifiable, description);
		mValue = mDefaultValue = defaultValue;
	}

	public DoubleOption(final DoubleOption other) {
		super(other.isOnlineModifiable(), other.getDescription());
		mValue = other.mValue;
		mDefaultValue = other.mDefaultValue;
	}

	@Override
	public Option copy() {
		return new DoubleOption(this);
	}

	@Override
	public void set(final Object value) {
		if (value instanceof Number) {
			mValue = ((Number) value).doubleValue();
		} else if (value instanceof String) {
			try {
				mValue = Double.parseDouble((String) value);
			} catch (final NumberFormatException nfe) {
				throw new SMTLIBException(nfe.getMessage());
			}
		} else {
			throw new SMTLIBException("Not a number: " + value);
		}
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
