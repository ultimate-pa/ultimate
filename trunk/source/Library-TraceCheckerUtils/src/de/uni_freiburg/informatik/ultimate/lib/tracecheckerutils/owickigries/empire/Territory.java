/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Set;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */

public final class Territory<PLACE, LETTER> {

	/**
	 * Set of regions in Territory.
	 */
	private final Set<Region> mTerritory;

	public Territory(final Set<Region> regions) {
		mTerritory = regions;
	}

	/**
	 * @return Set of regions in Territory.
	 */
	public Set<Region> getRegions() {
		return mTerritory;
	}

	/**
	 * Adds the specified set of regions into the territory.
	 *
	 * @param Set
	 *            of regions
	 */
	public void addRegion(final Set<Region> regions) {
		mTerritory.addAll(regions);
	}

	/**
	 * Adds the specified region of places into territory.
	 *
	 * @param region
	 */
	public void addRegion(final Region region) {
		mTerritory.add(region);
	}

	// Corelation at level of places call

}
