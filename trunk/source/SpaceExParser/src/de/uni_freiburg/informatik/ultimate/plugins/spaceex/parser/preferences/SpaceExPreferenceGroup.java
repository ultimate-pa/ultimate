/*
 * Copyright (C) 2017 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 *
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import java.util.Collections;
import java.util.Map;

public class SpaceExPreferenceGroup extends PreferenceGroup {
	
	private final Map<String, String> mInitialLocations;
	
	public SpaceExPreferenceGroup(final Map<String, String> initialLocations, final String initialVariableInfix,
			final int id) {
		super(id, initialVariableInfix);
		mInitialLocations = (initialLocations != null) ? initialLocations : Collections.emptyMap();
	}
	
	public Map<String, String> getInitialLocations() {
		return mInitialLocations;
	}
	
	@Override
	public String toString() {
		return "{Locations: " + mInitialLocations + "\n Variables: " + mVariableInfix + "\n Id: " + mId + "}";
	}
	
}
