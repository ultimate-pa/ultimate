/*
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
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceManager;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Generator that creates a parallel composition from {@link HybridAutomaton} instances.
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * 
 */
public class ParallelCompositionGenerator {
	
	private final ILogger mLogger;
	private Set<String> mGlobalConstsMerge;
	private Set<String> mGlobalParamsMerge;
	private Set<String> mLocalConstsMerge;
	private Set<String> mLocalParamsMerge;
	private Set<String> mLabelsMerge;
	private Set<String> mGlobalLabels;
	private Map<String, Set<String>> mLocalLabels;
	private Map<Integer, Location> mLocationsMerge;
	private Location mInitialLocationMerge;
	private List<Transition> mTransitionMerge;
	private AtomicInteger mIdCounter;
	private Map<Set<Location>, Integer> mCreatedLocations;
	private final Stack<List<Location>> mComputationStackNWay;
	private Set<Set<Location>> mVisitedLocations;
	private Set<String> mForbiddenLocations;
	private final SpaceExPreferenceManager mPreferencemanager;
	
	public ParallelCompositionGenerator(final ILogger logger, final SpaceExPreferenceManager preferenceManager) {
		mLogger = logger;
		mGlobalConstsMerge = new HashSet<>();
		mGlobalParamsMerge = new HashSet<>();
		mLocalConstsMerge = new HashSet<>();
		mLocalParamsMerge = new HashSet<>();
		mLabelsMerge = new HashSet<>();
		mGlobalLabels = new HashSet<>();
		mLocalLabels = new HashMap<>();
		mLocationsMerge = new HashMap<>();
		mTransitionMerge = new ArrayList<>();
		mCreatedLocations = new HashMap<>();
		mIdCounter = new AtomicInteger(0);
		mComputationStackNWay = new Stack<>();
		mVisitedLocations = new HashSet<>();
		mForbiddenLocations = new HashSet<>();
		mPreferencemanager = preferenceManager;
	}
	
	public HybridAutomaton computeParallelCompositionNWay(final Map<HybridAutomaton, Location> automataAndInitial) {
		// name
		final String nameMerge = generateName(automataAndInitial);
		// labels are merged with union
		mergeParametersNWay(automataAndInitial.keySet());
		// 1. get the initial locations, merge them
		// 2. get the outgoing transitions from the initials
		// 3. compare and merge the outgoing transitions
		// 4. Repeat
		final List<Location> initialLocations = new ArrayList<>(automataAndInitial.values());
		mInitialLocationMerge = getLocationNWay(initialLocations);
		// Add the initial locations to a Stack which holds LocationPair objects
		mLogger.info("Pushing: " + initialLocations);
		mComputationStackNWay.push(initialLocations);
		// compute the parallel composition starting from the initial location
		createLocationsAndTransitionsNWay();
		final HybridAutomaton hybAut = new HybridAutomaton(nameMerge, mLocationsMerge, mInitialLocationMerge,
				mTransitionMerge, mLocalParamsMerge, mLocalConstsMerge, mGlobalParamsMerge, mGlobalConstsMerge,
				mLabelsMerge, mLogger);
		// clean up
		cleanUpMembers();
		return hybAut;
	}
	
	private String generateName(final Map<HybridAutomaton, Location> automataAndInitial) {
		String name = "";
		final Set<HybridAutomaton> automata = automataAndInitial.keySet();
		for (final HybridAutomaton aut : automata) {
			if (!name.isEmpty()) {
				name += "||";
			}
			name += aut.getName();
		}
		return name;
	}
	
	private void createLocationsAndTransitionsNWay() {
		while (!mComputationStackNWay.isEmpty()) {
			final List<Location> currentLocs = mComputationStackNWay.pop();
			final Set<Location> locsSet = new HashSet<>(currentLocs);
			if (mVisitedLocations.contains(locsSet)) {
				continue;
			}
			final Location source = getLocationNWay(currentLocs);
			mVisitedLocations.add(locsSet);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("CURRENT NODE:" + source.getName());
				mLogger.debug("ADDING TO VISITED:" + currentLocs);
				mLogger.debug("VISITED: " + mVisitedLocations);
			}
			// get all outgoing transitions and set labels,guards,updates
			final List<Transition> allOutgoing = getAllOutgoingTransitions(currentLocs);
			// if there are no outgoing transitions in either location, we can simply merge them and continue.
			if (allOutgoing.isEmpty()) {
				continue;
			} else {
				// if there is a transition, get it
				// if there is no transition, the target is the source.
				final List<Transition> synchronizations = getSynchronizations(allOutgoing);
				if (!synchronizations.isEmpty()) {
					// transitions
					final List<Location> targets = new ArrayList<>();
					final Map<Location, Triple<String, String, String>> targetLocs =
							calculateTargetsForSync(synchronizations, currentLocs);
					for (final Entry<Location, Triple<String, String, String>> target : targetLocs.entrySet()) {
						final Location targetLoc = target.getKey();
						final String label = target.getValue().getFirst();
						final String guard = target.getValue().getSecond();
						final String update = target.getValue().getThird();
						final Transition trans = createTransition(source, targetLoc, label, guard, update);
						if (!mTransitionMerge.contains(trans)) {
							source.addOutgoingTransition(trans);
							targetLoc.addIncomingTransition(trans);
							mTransitionMerge.add(trans);
							targets.add(targetLoc);
						}
					}
				} else {
					// Create N target locations
					// if the locations exists, get it, else create a new one from the location pairs
					final Map<Location, Triple<String, String, String>> targetLocs =
							calculateTargetsForNonSync(allOutgoing, currentLocs);
					for (final Entry<Location, Triple<String, String, String>> target : targetLocs.entrySet()) {
						final Location targetLoc = target.getKey();
						final String label = target.getValue().getFirst();
						final String guard = target.getValue().getSecond();
						final String update = target.getValue().getThird();
						final Transition trans = createTransition(source, targetLoc, label, guard, update);
						source.addOutgoingTransition(trans);
						targetLoc.addIncomingTransition(trans);
						mTransitionMerge.add(trans);
					}
				}
			}
		}
	}
	
	private List<Location> getMissingLocs(final List<Location> currentLocs, final List<Location> forbiddenSources) {
		final List<Location> missing = new ArrayList<>();
		for (final Location loc : currentLocs) {
			if (!forbiddenSources.contains(loc)) {
				missing.add(loc);
			}
		}
		return missing;
	}
	
	private List<Transition> getSynchronizations(final List<Transition> allOutgoing) {
		final List<Transition> syncs = new ArrayList<>();
		final String synclabel = "";
		for (final Transition trans : allOutgoing) {
			final String lab = (synclabel.isEmpty()) ? trans.getLabel() : synclabel;
			if (mGlobalLabels.contains(lab)) {
				syncs.add(trans);
			}
		}
		return (syncs.size() > 1) ? syncs : new ArrayList<>();
	}
	
	private Map<Location, Triple<String, String, String>> calculateTargetsForNonSync(final List<Transition> allOutgoing,
			final List<Location> currentLocs) {
		final Map<Location, Triple<String, String, String>> targets = new HashMap<>();
		final String label = "";
		String guard = "";
		String update = "";
		for (int i = 0; i < allOutgoing.size(); i++) {
			final List<Location> mergeList = new ArrayList<>();
			final List<Location> forbiddenSources = new ArrayList<>();
			final Transition trans = allOutgoing.get(i);
			if (!mGlobalLabels.contains(trans.getLabel())) {
				mergeList.add(trans.getTarget());
				guard = intersectStrings(guard, trans.getGuard());
				update = intersectStrings(update, trans.getUpdate());
				forbiddenSources.add(trans.getSource());
				mergeList.addAll(getMissingLocs(currentLocs, forbiddenSources));
				final Location target = getLocationNWay(mergeList);
				if (!mComputationStackNWay.contains(mergeList)) {
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("Pushing to stack: " + mergeList);
					}
					mComputationStackNWay.push(mergeList);
				}
				final Triple<String, String, String> triple = new Triple<>(label, guard, update);
				targets.put(target, triple);
			}
		}
		return targets;
	}
	
	private Map<Location, Triple<String, String, String>>
			calculateTargetsForSync(final List<Transition> synchronizations, final List<Location> currentLocs) {
		final List<Location> targetLocs = new ArrayList<>();
		final List<Location> mergeList = new ArrayList<>();
		final List<Location> forbiddenSources = new ArrayList<>();
		final Map<Location, Triple<String, String, String>> targets = new HashMap<>();
		String label = "";
		String guard = "";
		String update = "";
		for (final Transition trans : synchronizations) {
			
			final Location target = trans.getTarget();
			mergeList.add(target);
			label = label.isEmpty() ? trans.getLabel() : label;
			guard = intersectStrings(guard, trans.getGuard());
			update = intersectStrings(update, trans.getUpdate());
			forbiddenSources.add(trans.getSource());
			
		}
		mergeList.addAll(getMissingLocs(currentLocs, forbiddenSources));
		final Location target = getLocationNWay(mergeList);
		final Triple<String, String, String> triple = new Triple<>(label, guard, update);
		targets.put(target, triple);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Pushing to stack: " + mergeList);
		}
		mComputationStackNWay.push(mergeList);
		return targets;
	}
	
	private List<Transition> getAllOutgoingTransitions(final List<Location> currentLocs) {
		final List<Transition> alloutgoing = new ArrayList<>();
		for (final Location loc : currentLocs) {
			alloutgoing.addAll(loc.getOutgoingTransitions());
		}
		return alloutgoing;
	}
	
	private Location getLocationNWay(final List<Location> mergeList) {
		final String locString = mergeList.toString();
		final Set<Location> locset = new HashSet<>(mergeList);
		Location loc;
		if (mCreatedLocations.containsKey(locset)) {
			final int locId = mCreatedLocations.get(locset);
			loc = mLocationsMerge.get(locId);
		} else {
			loc = mergeLocationsNWay(mIdCounter.incrementAndGet(), mergeList);
			mCreatedLocations.put(locset, mIdCounter.get());
			mLocationsMerge.put(mIdCounter.get(), loc);
		}
		// hack TODO: change this
		if (loc == null) {
			loc = mergeLocationsNWay(mIdCounter.incrementAndGet(), mergeList);
			mCreatedLocations.put(locset, mIdCounter.get());
			mLocationsMerge.put(mIdCounter.get(), loc);
		}
		return loc;
	}
	
	private Location mergeLocationsNWay(final int incrementAndGet, final List<Location> mergeList) {
		String name = "loc_";
		String invariant = "";
		String flow = "";
		boolean forbidden = false;
		final List<String> forbiddenLocNames = new ArrayList<>();
		mergeList.sort(Comparator.comparing(Location::getInvariant));
		// merge each locations invariant,flow and name
		for (final Location loc : mergeList) {
			name += loc.getName() + "_";
			invariant = intersectStrings(invariant, loc.getInvariant());
			flow = intersectStrings(flow, loc.getFlow());
			if (loc.isForbidden()) {
				forbidden = true;
				forbiddenLocNames.add(loc.getName());
			}
		}
		// create locations
		final Location merged = new Location(incrementAndGet, name);
		merged.setInvariant(invariant);
		merged.setFlow(flow);
		if (forbidden) {
			merged.setForbidden(true);
			for (final String locname : forbiddenLocNames) {
				if (mPreferencemanager.getForbiddenToForbiddenlocs().containsKey(locname)) {
					mPreferencemanager.getForbiddenToForbiddenlocs().get(locname).add(name);
					final List<String> oldloclist = mPreferencemanager.getForbiddenToForbiddenlocs().get(locname);
					mPreferencemanager.getForbiddenToForbiddenlocs().put(name, oldloclist);
				}
			}
		}
		return merged;
	}
	
	private void mergeParametersNWay(final Set<HybridAutomaton> automata) {
		for (final HybridAutomaton aut : automata) {
			mLocalConstsMerge.addAll(aut.getGlobalConstants());
			mLocalConstsMerge.addAll(aut.getLocalConstants());
			mLocalParamsMerge.addAll(aut.getGlobalParameters());
			mLocalParamsMerge.addAll(aut.getLocalParameters());
			mLabelsMerge.addAll(aut.getLabels());
		}
		anaylseLabels(automata);
	}
	
	// function that determines which labels are globally used.
	private void anaylseLabels(final Set<HybridAutomaton> automata) {
		final Map<String, Integer> labelCount = new HashMap<>();
		for (final HybridAutomaton aut : automata) {
			final Set<String> labels = aut.getLabels();
			for (final String label : labels) {
				final int count = labelCount.containsKey(label) ? labelCount.get(label) : 0;
				labelCount.put(label, count + 1);
			}
		}
		labelCount.forEach((lab, val) -> {
			if (val > 1) {
				mGlobalLabels.add(lab);
			}
		});
	}
	
	private void cleanUpMembers() {
		// clean up all members because necessary for multiple parallel compositions
		// dirty hack
		mGlobalConstsMerge = new HashSet<>();
		mGlobalParamsMerge = new HashSet<>();
		mLocalConstsMerge = new HashSet<>();
		mLocalParamsMerge = new HashSet<>();
		mLabelsMerge = new HashSet<>();
		mGlobalLabels = new HashSet<>();
		mLocalLabels = new HashMap<>();
		mLocationsMerge = new HashMap<>();
		mTransitionMerge = new ArrayList<>();
		mCreatedLocations = new HashMap<>();
		mIdCounter = new AtomicInteger(0);
		mVisitedLocations = new HashSet<>();
		mForbiddenLocations = new HashSet<>();
	}
	
	/**
	 * Function that creates a transition
	 * 
	 * @param source
	 * @param target
	 * @param label
	 * @param guard
	 * @param update
	 * @return
	 */
	private Transition createTransition(final Location source, final Location target, final String label,
			final String guard, final String update) {
		final Transition trans = new Transition(source, target);
		trans.setLabel(label);
		trans.setGuard(guard);
		trans.setUpdate(update);
		return trans;
	}
	
	/*
	 * Helper function to merge two strings into a string of the form "str1 && str2" Used for intersecting guards and
	 * updates of transitions in this class.
	 */
	private String intersectStrings(final String str1, final String str2) {
		String intersection;
		final String string1 = (str1 == null) ? "" : str1;
		final String string2 = (str2 == null) ? "" : str2;
		if (string1.equals(string2) || (!"".equals(string1) && "".equals(string2))) {
			intersection = string1;
		} else if (!"".equals(string1) && !"".equals(string2)) {
			intersection = string1 + " && " + string2;
		} else if ("".equals(string1) && !"".equals(string2)) {
			intersection = string2;
		} else {
			intersection = "";
		}
		return intersection;
	}
}
