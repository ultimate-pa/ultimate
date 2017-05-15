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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.LocationType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ParamType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.TransitionType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceContainer;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceGroup;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridPreprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridSystemHelper;

public class HybridAutomaton {
	
	private final String mName;
	private final String mSystem;
	private final Set<String> mGlobalParameters;
	private final Set<String> mLocalParameters;
	private final Set<String> mGlobalConstants;
	private final Set<String> mLocalConstants;
	private final Set<String> mLabels;
	private final Map<Integer, Location> mLocations;
	private final Map<String, Integer> mNametoId;
	// group -> init
	private final Map<Integer, Location> mGroupToInitialLocation;
	private final Location mDefaultInitialLocation;
	private final List<Transition> mTransitions;
	private final ILogger mLogger;
	private SpaceExPreferenceContainer mPreferenceContainer;
	
	protected HybridAutomaton(final String nameInSystem, final String systemName, final ComponentType automaton,
			final ILogger logger, final SpaceExPreferenceContainer preferenceContainer) {
		if (!automaton.getBind().isEmpty()) {
			throw new UnsupportedOperationException(
					"The input automaton must be a hybrid automaton, not a system template.");
		}
		mName = nameInSystem.isEmpty() ? automaton.getId() : nameInSystem;
		mSystem = systemName;
		mLocations = new HashMap<>();
		mTransitions = new ArrayList<>();
		mGlobalParameters = new HashSet<>();
		mLocalParameters = new HashSet<>();
		mGlobalConstants = new HashSet<>();
		mLocalConstants = new HashSet<>();
		mLabels = new HashSet<>();
		mLogger = logger;
		mPreferenceContainer = preferenceContainer;
		mNametoId = new HashMap<>();
		mGroupToInitialLocation = new HashMap<>();
		
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
		if (!mLocations.isEmpty()) {
			// init location default
			mDefaultInitialLocation = mLocations.values().iterator().next();
			// init locations for pref groups
			if (preferenceContainer != null) {
				final Map<Integer, SpaceExPreferenceGroup> prefGroups = mPreferenceContainer.getPreferenceGroups();
				prefGroups.forEach((id, group) -> {
					mGroupToInitialLocation.put(id, getInitialLocationFromGroup(group.getInitialLocations()));
				});
			}
		} else {
			throw new IllegalStateException(
					"Automaton with the name " + mName + "(sys: " + systemName + ") does not have any locations.");
		}
	}
	
	protected HybridAutomaton(final String name, final String systemName, final Map<Integer, Location> locations,
			final Location initialLocation, final List<Transition> transitions, final Set<String> localParameters,
			final Set<String> localConstants, final Set<String> globalParameters, final Set<String> globalConstants,
			final Set<String> labels, final ILogger logger) {
		mName = name;
		mSystem = systemName;
		mLocations = (locations != null) ? locations : Collections.emptyMap();
		mGroupToInitialLocation = Collections.emptyMap();
		mDefaultInitialLocation = initialLocation;
		mTransitions = (transitions != null) ? transitions : Collections.emptyList();
		mGlobalParameters = (globalParameters != null) ? globalParameters : Collections.emptySet();
		mLocalParameters = (localParameters != null) ? localParameters : Collections.emptySet();
		mGlobalConstants = (globalConstants != null) ? globalConstants : Collections.emptySet();
		mLocalConstants = (localConstants != null) ? localConstants : Collections.emptySet();
		mLabels = (labels != null) ? labels : Collections.emptySet();
		mLogger = logger;
		mNametoId = new HashMap<>();
		for (final Location location : mLocations.values()) {
			mNametoId.put(location.getName(), location.getId());
		}
	}
	
	private Location getInitialLocationFromGroup(final Map<String, String> initLocs) {
		if (initLocs == null) {
			return mDefaultInitialLocation;
		}
		final String initLocName = initLocs.get(mName);
		if (mNametoId.containsKey(initLocName)) {
			final int nameToId = mNametoId.get(initLocName);
			return mLocations.get(nameToId);
		} else {
			return mDefaultInitialLocation;
		}
	}
	
	private void addLocation(final LocationType location) {
		if (mLocations.containsKey(location.getId())) {
			throw new IllegalArgumentException(
					"The location " + location.getId() + " is already part of the automaton.");
		}
		
		final Location newLoc = new Location(location);
		newLoc.setInvariant(HybridPreprocessor.preprocessStatement(location.getInvariant()));
		newLoc.setFlow(HybridPreprocessor.preprocessStatement(location.getFlow()));
		if (mPreferenceContainer != null && mPreferenceContainer.isLocationForbidden(mName, newLoc.getName())) {
			newLoc.setForbidden(true);
			mPreferenceContainer.getForbiddenGroups().forEach(forb -> {
				if (forb.getLocations().containsKey(mName)
						&& forb.getLocations().get(mName).contains(newLoc.getName())) {
					newLoc.setForbiddenConstraint(HybridPreprocessor.preprocessStatement(forb.getVariableInfix()));
				}
			});
		} else if (mPreferenceContainer != null) {
			mPreferenceContainer.getForbiddenGroups().forEach(forb -> {
				if (forb.hasVariables() && !forb.hasLocations()) {
					newLoc.setForbiddenConstraint(HybridPreprocessor.preprocessStatement(forb.getVariableInfix()));
				}
			});
		}
		
		mLocations.put(newLoc.getId(), newLoc);
		mNametoId.put(newLoc.getName(), newLoc.getId());
		
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("[" + mName + "]: Added location: " + newLoc);
		}
	}
	
	private void addTransition(final TransitionType trans) {
		final Location source = mLocations.get(trans.getSource());
		final Location target = mLocations.get(trans.getTarget());
		
		if (source == null || target == null) {
			throw new UnsupportedOperationException("The source or target location referenced by transition "
					+ trans.getSource() + " --> " + trans.getTarget() + " is not present.");
		}
		
		final Transition newTrans = new Transition(source, target);
		newTrans.setGuard(HybridPreprocessor.preprocessStatement(trans.getGuard()));
		newTrans.setLabel(trans.getLabel());
		newTrans.setUpdate(HybridPreprocessor.preprocessStatement(trans.getAssignment()));
		
		mTransitions.add(newTrans);
		
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("[" + mName + "]: Added transition: " + newTrans);
		}
	}
	
	/**
	 * Function that renames constants according to the replacements the preference manager calculated.
	 */
	public void renameReplacedVariables() {
		// get the map which contains all renames that have to be made.
		final Map<String, Map<String, String>> requiresRename = mPreferenceContainer.getRequiresRename();
		// split the name of the system the automaton belongs to into parts.
		final String[] systemNameParts = mSystem.split("\\.");
		// the deepest part of the system-name has the highest priority.
		String highestPriority = "";
		for (final String systemNamePart : systemNameParts) {
			if (requiresRename.containsKey(systemNamePart)) {
				highestPriority = systemNamePart;
			}
		}
		if (requiresRename.containsKey(mName) || requiresRename.containsKey(highestPriority)) {
			Map<String, String> reverse = null;
			// reverse map so we can use an existing function instead of writing
			// a new one.
			if (requiresRename.containsKey(mName)) {
				reverse = requiresRename.get(mName).entrySet().stream()
						.collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));
			} else if (requiresRename.containsKey(highestPriority)) {
				reverse = requiresRename.get(highestPriority).entrySet().stream()
						.collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));
			}
			if (reverse != null) {
				renameAccordingToBinds(reverse);
			} else {
				mLogger.warn("nothing to rename in automaton with id: " + mName + " which belongs to system with id:"
						+ mSystem);
			}
		}
	}
	
	/**
	 * Function that renames variables and labels according to a systems binds.
	 *
	 * @param autBinds
	 * @return
	 */
	public void renameAccordingToBinds(final Map<String, String> autBinds) {
		if (autBinds == null) {
			return;
		}
		final List<String> processLater = new ArrayList<>();
		autBinds.forEach((glob, loc) -> {
			if (autBinds.containsValue(glob)) {
				processLater.add(glob);
			} else {
				renameAutomaton(loc, glob);
			}
		});
		processLater.forEach(glob -> {
			final String loc = autBinds.get(glob);
			renameAutomaton(loc, glob);
		});
	}
	
	private void renameAutomaton(final String loc, final String glob) {
		if (mLabels.contains(loc)) {
			// first of all remove the local name from labels and add the global
			// name
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
	}
	
	/*
	 * Function that renames variables of guards and updates of transitions
	 */
	private void renameTransitionVariables(final String loc, final String glob) {
		mTransitions.forEach(trans -> {
			String guard = trans.getGuard() != null ? trans.getGuard() : "";
			guard = guard.replaceAll("\\b" + loc + "\\b", glob);
			trans.setGuard(guard);
			String update = trans.getUpdate() != null ? trans.getUpdate() : "";
			update = update.replaceAll("\\b" + loc + "\\b", glob);
			trans.setUpdate(update);
		});
	}
	
	/*
	 * Function that renames invariant and flow of a location
	 */
	private void renameLocationVariables(final String loc, final String glob) {
		mLocations.forEach((id, location) -> {
			String invariant = (location.getInvariant() != null) ? location.getInvariant() : "";
			invariant = invariant.replaceAll("\\b" + loc + "\\b", glob);
			location.setInvariant(invariant);
			String flow = (location.getFlow() != null) ? location.getFlow() : "";
			flow = flow.replaceAll("\\b" + loc + "\\b", glob);
			location.setFlow(flow);
		});
	}
	
	/*
	 * function that replaces a value in a set
	 */
	private void replaceValueInSet(final Set<String> set, final String loc, final String glob) {
		set.remove(loc);
		set.add(glob);
	}
	
	/*
	 * function that renames labels in transitions
	 */
	private void renameTransitionLabels(final String loc, final String glob) {
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
				.append(mGroupToInitialLocation.toString() + "\n").append(indent).append("transitions: ")
				.append(mTransitions.toString());
		return sb.toString();
	}
	
	public Location getInitialLocation() {
		if (mGroupToInitialLocation.size() == 1) {
			return mGroupToInitialLocation.values().iterator().next();
		} else {
			return mDefaultInitialLocation;
		}
	}
	
	public Location getInitialLocationForGroup(final Integer groupID) {
		if (groupID == null) {
			return mDefaultInitialLocation;
		}
		if (mGroupToInitialLocation.containsKey(groupID)) {
			return mGroupToInitialLocation.get(groupID);
		} else {
			mLogger.info("No initial location for group id: " + groupID + " returning default loc");
			return mDefaultInitialLocation;
		}
	}
	
	public Map<String, Integer> getNametoId() {
		return mNametoId;
	}
}
