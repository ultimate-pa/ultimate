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

import java.lang.reflect.Field;
import java.lang.reflect.Parameter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.LocationType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ParamType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.TransitionType;

public class HybridAutomaton extends SpaceExElement {
	private final Set<String> mGlobalParameters;
	private final Set<String> mLocalParameters;
	private final Set<String> mGlobalConstants;
	private final Set<String> mLocalConstants;
	private final Set<String> mLabels;
	private final Map<Integer, Location> mLocations;
	private final List<Transition> mTransitions;

	private final ILogger mLogger;

	public HybridAutomaton(ComponentType automaton, ILogger logger) {
		if (!automaton.getBind().isEmpty()) {
			throw new UnsupportedOperationException(
			        "The input automaton must be a hybrid automaton, not a system template.");
		}

		mLocations = new HashMap<>();
		mTransitions = new ArrayList<>();
		mGlobalParameters = new HashSet<>();
		mLocalParameters = new HashSet<>();
		mGlobalConstants = new HashSet<>();
		mLocalConstants = new HashSet<>();
		mLabels = new HashSet<>();

		mLogger = logger;

		for (final ParamType param : automaton.getParam()) {
			addParameter(param);
		}

		for (final LocationType loc : automaton.getLocation()) {
			addLocation(loc);
		}

		for (final TransitionType trans : automaton.getTransition()) {
			addTransition(trans);
		}
	}

	private void addParameter(ParamType param) {
		if (mGlobalParameters.contains(param.getName())) {
			throw new IllegalArgumentException(
			        "The parameter " + param.getName() + " is already part of the automaton.");
		}

		final String name = param.getName();

		switch (param.getType()) {
		case "real":
			switch (param.getDynamics()) {
			case "any":
				if (param.isLocal()) {
					addParameterToSet(name, mLocalParameters);
				} else {
					addParameterToSet(name, mGlobalParameters);
				}
				break;
			case "const":
				if (param.isLocal()) {
					addParameterToSet(name, mLocalConstants);
				} else {
					addParameterToSet(name, mGlobalConstants);
				}
				break;
			default:
				throw new UnsupportedOperationException("The parameter type " + param.getType() + " is not supported.");
			}
			break;
		case "label":
			addParameterToSet(name, mLabels);
			break;
		default:
			throw new IllegalArgumentException("The parameter type " + param.getType() + " is unknown.");
		}
	}

	private void addParameterToSet(final String name, Collection<String> collection) {
		if (!collection.add(name)) {
			mLogger.warn("The variable with name " + name + " is already present in the set.");
		}
	}

	private void addLocation(LocationType location) {
		if (mLocations.containsKey(location.getId())) {
			throw new IllegalArgumentException(
			        "The location " + location.getId() + " is already part of the automaton.");
		}

		final Location newLoc = new Location(location);
		newLoc.setInvariant(location.getInvariant());
		newLoc.setFlow(location.getFlow());

		mLocations.put(newLoc.getId(), newLoc);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Added location: " + newLoc);
		}
	}

	private void addTransition(TransitionType trans) {
		final Location source = mLocations.get(trans.getSource());
		final Location target = mLocations.get(trans.getTarget());

		if (source == null || target == null) {
			throw new UnsupportedOperationException("The source or target location referenced by transition "
			        + trans.getSource() + " --> " + trans.getTarget() + " is not present.");
		}

		final Transition newTrans = new Transition(source, target);
		newTrans.setGuard(trans.getGuard());
		newTrans.setLabel(trans.getLabel());
		newTrans.setUpdate(trans.getAssignment());

		mTransitions.add(newTrans);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Added transition: " + newTrans);
		}
	}
}
