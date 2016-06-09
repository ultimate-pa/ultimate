/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.LocationType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ParamType;

public class HybridAutomaton extends SpaceExElement {
	// Params
	private final Map<String, ParameterType> mParameters;

	// Consts

	// Labels

	// Locations
	private final Map<Integer, Location> mLocations;

	// Transitions
	private final List<Transition> mTransitions;

	public HybridAutomaton(ComponentType automaton) {

		mLocations = new HashMap<Integer, Location>();
		mTransitions = new ArrayList<Transition>();
		mParameters = new HashMap<String, ParameterType>();

		for (final LocationType loc : automaton.getLocation()) {
			addLocation(loc);
		}

		for (final ParamType param : automaton.getParam()) {
			addParameter(param);
		}
	}

	private void addParameter(ParamType param) {
		if (mParameters.containsKey(param.getName())) {
			throw new IllegalArgumentException("The parameter " + param.getName()
			        + " is already part of the automaton.");
		}

		switch (param.getType()) {
		case "real":
			// Const
			// Dynamic
			break;
		case "label":
			break;
		default:
			throw new IllegalArgumentException("The parameter type " + param.getType() + " is unknown.");
		}
	}

	private void addLocation(LocationType location) {
		if (mLocations.containsKey(location.getId())) {
			throw new IllegalArgumentException("The location " + location.getId()
			        + " is already part of the automaton.");
		}

		final Location newLoc = new Location(location);

		mLocations.put(newLoc.getId(), newLoc);
	}
}
