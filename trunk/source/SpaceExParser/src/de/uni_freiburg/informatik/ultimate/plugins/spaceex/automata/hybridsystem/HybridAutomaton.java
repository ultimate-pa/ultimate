/*
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem;

import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceManager;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridSystemHelper;

public class HybridAutomaton {
	
	private final String mName;
	private final Set<String> mGlobalParameters;
	private final Set<String> mLocalParameters;
	private final Set<String> mGlobalConstants;
	private final Set<String> mLocalConstants;
	private final Set<String> mLabels;
	private final Map<Integer, Location> mLocations;
	private final Location mInitialLocation;
	private final List<Transition> mTransitions;
	private final ILogger mLogger;
	private SpaceExPreferenceManager mPreferenceManager;
	
	protected HybridAutomaton(ComponentType automaton, ILogger logger, SpaceExPreferenceManager preferenceManager) {
		if (!automaton.getBind().isEmpty()) {
			throw new UnsupportedOperationException(
					"The input automaton must be a hybrid automaton, not a system template.");
		}
		mName = automaton.getId();
		mLocations = new HashMap<>();
		mTransitions = new ArrayList<>();
		mGlobalParameters = new HashSet<>();
		mLocalParameters = new HashSet<>();
		mGlobalConstants = new HashSet<>();
		mLocalConstants = new HashSet<>();
		mLabels = new HashSet<>();
		mLogger = logger;
		mPreferenceManager = preferenceManager;
		
		for (final ParamType param : automaton.getParam()) {
			HybridSystemHelper.addParameter(param, mLocalParameters, mGlobalParameters, mLocalConstants,
					mGlobalConstants, mLabels, mLogger);
		}
		
		for (final LocationType loc : automaton.getLocation()) {
			addLocation(loc);
		}
		
		for (final TransitionType trans : automaton.getTransition()) {
			addTransition(trans);
		}
		// if initial location is simply the first location.
		mInitialLocation = mLocations.get(1);
	}
	
	protected HybridAutomaton(String name, Map<Integer, Location> locations, Location initialLocation,
			List<Transition> transitions, Set<String> localParameters, Set<String> localConstants,
			Set<String> globalParameters, Set<String> globalConstants, Set<String> labels, ILogger logger) {
		mName = name;
		mLocations = locations;
		mInitialLocation = initialLocation;
		mTransitions = transitions;
		mGlobalParameters = globalParameters;
		mLocalParameters = localParameters;
		mGlobalConstants = globalConstants;
		mLocalConstants = localConstants;
		mLabels = labels;
		mLogger = logger;
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
			mLogger.debug("[" + mName + "]: Added location: " + newLoc);
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
			mLogger.debug("[" + mName + "]: Added transition: " + newTrans);
		}
	}
	
	/**
	 * Function that renames variables and labels according to a systems binds.
	 * 
	 * @param autBinds
	 * @return
	 */
	public Map<String, String> renameAccordingToBinds(Map<String, String> autBinds) {
		final Map<String, String> newBinds = new HashMap<>();
		autBinds.forEach((glob, loc) -> {
			if (mLabels.contains(loc)) {
				// first of all remove the local name from labels and add the global name
				replaceValueInSet(mLabels, loc, glob);
				// second change the labelnames of the transitions.
				renameTransitionLabels(loc, glob);
			} else if (mGlobalParameters.contains(loc)) {
				// first replace values
				replaceValueInSet(mGlobalParameters, loc, glob);
				// then rename in invariants and flow of locations
				renameLocationVariables(loc, glob);
				// then rename in guards and assignments of transitions
				renameTransitionVariables(loc, glob);
			} else if (mGlobalConstants.contains(loc)) {
				replaceValueInSet(mGlobalConstants, loc, glob);
				renameLocationVariables(loc, glob);
				renameTransitionVariables(loc, glob);
			} else if (mLocalParameters.contains(loc)) {
				replaceValueInSet(mLocalParameters, loc, glob);
				renameLocationVariables(loc, glob);
				renameTransitionVariables(loc, glob);
			} else if (mLocalConstants.contains(loc)) {
				replaceValueInSet(mLocalConstants, loc, glob);
				renameLocationVariables(loc, glob);
				renameTransitionVariables(loc, glob);
			}
			newBinds.put(glob, glob);
		});
		return newBinds;
	}
	
	/*
	 * Function that renames variables of guards and updates of transitions
	 */
	private void renameTransitionVariables(String loc, String glob) {
		mTransitions.forEach(trans -> {
			String guard = trans.getGuard() != null ? trans.getGuard() : "";
			guard = guard.replaceAll(loc, glob);
			trans.setGuard(guard);
			String update = trans.getUpdate() != null ? trans.getUpdate() : "";
			update = update.replaceAll(loc, glob);
			trans.setUpdate(update);
		});
	}
	
	/*
	 * Function that renames invariant and flow of a location
	 */
	private void renameLocationVariables(String loc, String glob) {
		mLocations.forEach((id, location) -> {
			String invariant = (location.getInvariant() != null) ? location.getInvariant() : "";
			invariant = invariant.replaceAll(loc, glob);
			location.setInvariant(invariant);
			String flow = (location.getFlow() != null) ? location.getFlow() : "";
			flow = flow.replaceAll(loc, glob);
			location.setFlow(flow);
		});
	}
	
	/*
	 * function that replaces a value in a set
	 */
	private void replaceValueInSet(Set<String> set, String loc, String glob) {
		set.remove(loc);
		set.add(glob);
	}
	
	/*
	 * function that renames labels in transitions
	 */
	private void renameTransitionLabels(String loc, String glob) {
		mTransitions.forEach(trans -> {
			if (trans.getLabel() != null && trans.getLabel().equals(loc)) {
				trans.setLabel(glob);
			}
		});
		
	}
	
	public String getName() {
		return mName;
	}
	
	public Map<Integer, Location> getLocations() {
		return mLocations;
	}
	
	public List<Transition> getTransitions() {
		return mTransitions;
	}
	
	public Set<String> getGlobalParameters() {
		return mGlobalParameters;
	}
	
	public Set<String> getGlobalConstants() {
		return mGlobalConstants;
	}
	
	public Set<String> getLocalConstants() {
		return mLocalConstants;
	}
	
	public Set<String> getLocalParameters() {
		return mLocalParameters;
	}
	
	public Set<String> getLabels() {
		return mLabels;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final String indent = "    ";
		sb.append(mName).append(":\n ").append(indent).append("parameters: ")
				.append(mGlobalParameters.toString() + mLocalParameters.toString() + "\n").append(indent)
				.append("constants: ").append(mGlobalConstants.toString() + mLocalConstants.toString() + "\n")
				.append(indent).append("labels: ").append(mLabels.toString() + "\n").append(indent)
				.append("locations: ").append(mLocations.toString() + "\n").append(indent).append("initial Location: ")
				.append(mInitialLocation.toString() + "\n").append(indent).append("transitions: ")
				.append(mTransitions.toString());
		return sb.toString();
	}
	
	public Location getInitialLocation() {
		return mInitialLocation;
	}
}
