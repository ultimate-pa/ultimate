/*
 * Copyright (C) 2024 Helen Meyer (helen.anna.meyer@gmail.com)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessParser plug-in.
 *
 * The ULTIMATE WitnessParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

/**
 * Waypoints are the basic building blocks of entry-based violation witnesses. Technically a waypoint is a mapping with
 * our keys: type, location, constraint and action.
 *
 * @author Helen Meyer (helen.anna.meyer@gmail.com)
 */
public abstract class Waypoint {
	private final Constraint mConstraint;
	private final Location mLocation;

	public Waypoint(final Constraint constraint, final Location location) {
		mConstraint = constraint;
		mLocation = location;
	}

	public Constraint getConstraint() {
		return mConstraint;
	}

	public Location getLocation() {
		return mLocation;
	}

	public abstract String getType();

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getType()).append(' ').append(mLocation);
		if (mConstraint != null) {
			sb.append(": ").append(mConstraint);
		}
		return sb.toString();
	}
}
