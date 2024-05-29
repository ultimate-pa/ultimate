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

import java.util.List;

/**
 * Waypoints are organized into Segments. Each segment contains zero or more Waypoints with action "avoid" and exactly
 * one with action "follow"
 *
 * @author Helen Meyer (helen.anna.meyer@gmail.com)
 */
public class Segment {
	private final List<Waypoint> mAvoid;
	private final Waypoint mFollow;

	public Segment(final List<Waypoint> avoid, final Waypoint follow) {
		mAvoid = avoid;
		mFollow = follow;
	}

	public List<Waypoint> getAvoid() {
		return mAvoid;
	}

	public Waypoint getFollow() {
		return mFollow;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Segment: ");
		if (!mAvoid.isEmpty()) {
			sb.append("avoid:").append(mAvoid).append(", ");
		}
		return sb.append("follow: ").append(mFollow).toString();
	}

}
