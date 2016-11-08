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

/**
 * Base class for all options stored in an {@link OptionMap}.
 * @author Juergen Christ
 */
public abstract class Option {

	private final boolean mOnlineModifiable;
	private final String mDescription;
	
	public Option(boolean onlineModifiable, String description) {
		mOnlineModifiable = onlineModifiable;
		mDescription = description;
	}

	/**
	 * Set the value of this option.
	 * @param value The new value.
	 */
	public abstract void set(Object value);
	/**
	 * Get the value of this option.
	 * @return The current value of this option.
	 */
	public abstract Object get();
	/**
	 * Reset this option to its initial value.
	 */
	public abstract void reset();
	/**
	 * Get the default value of this option.
	 * @return The default value of this option.
	 */
	public abstract Object defaultValue();
	/**
	 * Can this option be modified after setLogic?
	 * @return <code>true</code> if this option can be modified after setLogic.
	 */
	public final boolean isOnlineModifiable() {
		return mOnlineModifiable;
	}
	/**
	 * Get the description of this option.
	 * @return The description of this option.
	 */
	public final String getDescription() {
		return mDescription;
	}

	/**
	 * Generate a copy of this option.  The copy should currently store the same
	 * value as this option.
	 * @return A copy of this option.
	 */
	public abstract Option copy();

	/**
	 * Called by the option map to indicate that the solver is now started.  The
	 * current values should be set as default values.
	 */
	public abstract void started();
}
