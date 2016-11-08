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
 * Boolean options.
 * @author Juergen Christ
 */
public class BooleanOption extends Option {

	private boolean mValue;
	private boolean mDefaultValue;

	public BooleanOption(boolean defaultValue, boolean onlineModifiable,
			String description) {
		super(onlineModifiable, description);
		mValue = mDefaultValue = defaultValue;
	}
	public BooleanOption(BooleanOption other) {
		super(other.isOnlineModifiable(), other.getDescription());
		mValue = other.mValue;
		mDefaultValue = other.mDefaultValue;
	}
	@Override
	public Option copy() {
		return new BooleanOption(this);
	}
	@Override
	public void set(Object value) {
		if (value instanceof Boolean) {
			mValue = ((Boolean) value).booleanValue();
		} else if (value instanceof String) {
			final String str = (String) value;
			if ("true".equalsIgnoreCase(str)) {
				mValue = true;
			} else if ("false".equalsIgnoreCase(str)) {
				mValue = false;
			} else {
				throw new SMTLIBException("Not a Boolean value: " + value);
			}
		} else {
			throw new SMTLIBException("Not a Boolean value: " + value);
		}
	}

	public final boolean getValue() { // NOPMD
		return mValue;
	}
	@Override
	public Object get() {
		return Boolean.valueOf(mValue);
	}

	@Override
	public void reset() {
		mValue = mDefaultValue;
	}

	@Override
	public Object defaultValue() {
		return Boolean.valueOf(mDefaultValue);
	}
	@Override
	public void started() {
		mDefaultValue = mValue;
	}

}
