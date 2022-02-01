/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.results;

/**
 * Result that says that all specifications were checked and hold. Use this also if there was not specification.
 *
 * @author Matthias Heizmann
 */
public class AllSpecificationsHoldResult extends AbstractResult {

	private final String mLongdescription;

	public AllSpecificationsHoldResult(final String plugin, final String longDescription) {
		super(plugin);
		mLongdescription = longDescription;
	}

	@Override
	public String getShortDescription() {
		return "All specifications hold";
	}

	@Override
	public String getLongDescription() {
		return mLongdescription;
	}

	/**
	 * Generate an {@link AllSpecificationsHoldResult} that contains a standardized long description.
	 *
	 * @param pluginName
	 *            The name of the reporting plugin.
	 * @param numberOfErrorLocations
	 *            The total number of error locations (all should be proven safe).
	 * @return
	 */
	public static AllSpecificationsHoldResult createAllSpecificationsHoldResult(final String pluginName,
			final int numberOfErrorLocations) {
		final String longDescription;
		if (numberOfErrorLocations <= 0) {
			longDescription = "We were not able to verify any"
					+ " specifiation because the program does not contain any specification.";
		} else {
			longDescription = Integer.toString(numberOfErrorLocations) + " specifications checked. All of them hold";
		}
		return new AllSpecificationsHoldResult(pluginName, longDescription);
	}
}
