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
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Generator that creates a parallel composition from {@link HybridAutomaton}
 * instances.
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
	private Map<Integer, Location> mLocationsMerge;
	private List<Transition> mTransitionMerge;
	private AtomicInteger mIdCounter;
	private Map<Set<Location>, Integer> mCreatedLocations;
	private final Deque<List<Location>> mComputationStackNWay;
	private Set<Set<Location>> mVisitedLocations;
	private final AtomicInteger mNameIDCounter;

	public ParallelCompositionGenerator(final ILogger logger) {
		mLogger = logger;
		mGlobalConstsMerge = new HashSet<>();
		mGlobalParamsMerge = new HashSet<>();
		mLocalConstsMerge = new HashSet<>();
		mLocalParamsMerge = new HashSet<>();
		mLabelsMerge = new HashSet<>();
		mGlobalLabels = new HashSet<>();
		mLocationsMerge = new HashMap<>();
		mTransitionMerge = new ArrayList<>();
		mCreatedLocations = new HashMap<>();
		mIdCounter = new AtomicInteger(0);
		mComputationStackNWay = new LinkedList<>();
		mVisitedLocations = new HashSet<>();
		mNameIDCounter = new AtomicInteger(0);
	}

	/**
	 * Function that calculates the parallel composition of N Automata
	 *
	 * @param automataAndInitial
	 * @return
	 */
	public HybridAutomaton computeParallelCompositionNWay(final Map<HybridAutomaton, Location> automataAndInitial) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("####################### STARTING PARALLEL COMPOSITION ###########################");
		}
		// name
		final String nameMerge = "MERGE" + mNameIDCounter.getAndIncrement();
		// labels are merged with union
		mergeParametersNWay(automataAndInitial.keySet());
		// 1. get the initial locations, merge them
		// 2. get the outgoing transitions from the initials
		// 3. compare and merge the outgoing transitions
		// 4. Repeat
		final List<Location> initialLocations = new ArrayList<>(automataAndInitial.values());
		final Location initialLocationMerge = getLocationNWay(initialLocations);
		// Add the initial locations to a Stack which holds LocationPair objects
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("###################### STACK UPDATE #########################");
			initialLocations.forEach(loc -> mLogger.debug("*" + loc));
			mLogger.debug("##################### STACK UPDATE END #######################");
		}
		mComputationStackNWay.push(initialLocations);
		// compute the parallel composition starting from the initial location
		createLocationsAndTransitionsNWay();
		final HybridAutomaton hybAut = new HybridAutomaton(nameMerge, "mergedSystem", mLocationsMerge,
				initialLocationMerge, mTransitionMerge, mLocalParamsMerge, mLocalConstsMerge, mGlobalParamsMerge,
				mGlobalConstsMerge, mLabelsMerge, mLogger);
		// clean up
		cleanUpMembers();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("####################### PARALLEL COMPOSITION END ###########################");
		}
		return hybAut;
	}

	// "main" function of the parallel composition.
	private void createLocationsAndTransitionsNWay() {
		while (!mComputationStackNWay.isEmpty()) {
			final List<Location> currentLocs = mComputationStackNWay.pop();
			final Set<Location> locsSet = new HashSet<>(currentLocs);
			if (mVisitedLocations.contains(locsSet)) {
				continue;
			}
			final Location source = getLocationNWay(currentLocs);
			mVisitedLocations.add(locsSet);
			// get all outgoing transitions and set labels,guards,updates
			final List<Transition> allOutgoing = getAllOutgoingTransitions(currentLocs);
			/*
			 * DEBUG START
			 */
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("CURRENT NODE:" + source.getName());
				mLogger.debug("############### ADDING SET TO VISITED ################");
				currentLocs.forEach(loc -> mLogger.debug("*" + loc));
				mLogger.debug("###########################################");
				// mLogger.debug("################### VISITED SETS
				// #######################");
				// for (final Set<Location> locs : mVisitedLocations) {
				// mLogger.debug("############### SET ################");
				// locs.forEach(loc -> mLogger.debug("*" + loc));
				// mLogger.debug("####################################");
				// }
				// mLogger.debug("#####################################################");
				mLogger.debug("############### OUTGOING TRANSITIONS ###############");
				for (final Transition t : allOutgoing) {
					mLogger.debug("*" + t);
				}
				mLogger.debug("#####################################################");
			}
			/*
			 * DEBUG END
			 */
			// if there are no outgoing transitions in either location, we can
			// simply merge them and continue.
			if (allOutgoing.isEmpty()) {
				continue;
			} else {
				// if there is a transition, get it
				// if there is no transition, the target is the source.
				final List<Transition> synchronizations = getSynchronizations(allOutgoing);
				if (!synchronizations.isEmpty()) {
					// transitions
					final Map<Location, Triple<String, String, String>> targetLocs = calculateTargetsForSync(
							synchronizations, currentLocs);
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
						}
					}
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("################## CURRENT TARGETS #####################");
						targetLocs.forEach((tar, info) -> {
							mLogger.debug("TARGET LOCATION:" + tar.getName());
							mLogger.debug("TRANSITION INFO: " + info);
						});
						mLogger.debug("################## CURRENT TARGETS END #################");
					}
				} else {
					// Create N target locations
					// if the locations exists, get it, else create a new one
					// from the location pairs
					final Map<Location, Triple<String, String, String>> targetLocs = calculateTargetsForNonSync(
							allOutgoing, currentLocs);
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
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("################## CURRENT TARGETS #####################");
						targetLocs.forEach((tar, info) -> {
							mLogger.debug("TARGET LOCATION:" + tar.getName());
							mLogger.debug("TRANSITION INFO: " + info);
						});
						mLogger.debug("################## CURRENT TARGETS END #################");
					}
				}
			}
		}
	}

	// helper function that adds source locations of transitions which are not
	// part of the set yet.
	private List<Location> getMissingLocs(final List<Location> currentLocs, final List<Location> forbiddenSources) {
		final List<Location> missing = new ArrayList<>();
		for (final Location loc : currentLocs) {
			if (!forbiddenSources.contains(loc)) {
				missing.add(loc);
			}
		}
		return missing;
	}

	// function that returns all synchronizations of a given list of
	// Transitions.
	private List<Transition> getSynchronizations(final List<Transition> allOutgoing) {
		final List<Transition> syncs = new ArrayList<>();
		String synclabel = "";
		for (final Transition trans : allOutgoing) {
			String lab;
			if (synclabel.isEmpty()) {
				lab = trans.getLabel();
				if (mGlobalLabels.contains(lab)) {
					synclabel = lab;
					syncs.add(trans);
				}
			} else {
				if (synclabel.equals(trans.getLabel())) {
					syncs.add(trans);
				}
			}
		}
		// we need at least two synchronizations.
		return (syncs.size() > 1) ? syncs : new ArrayList<>();
	}

	// function that returns the target locations of a non synchronization.
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
						mLogger.debug("###################### STACK UPDATE #########################");
						mergeList.forEach(loc -> mLogger.debug("*" + loc));
						mLogger.debug("##################### STACK UPDATE END #######################");
					}
					mComputationStackNWay.push(mergeList);
				}
				final Triple<String, String, String> triple = new Triple<>(label, guard, update);
				targets.put(target, triple);
			}
		}
		return targets;
	}

	// function that returns the target locations of a synchronization.
	private Map<Location, Triple<String, String, String>> calculateTargetsForSync(
			final List<Transition> synchronizations, final List<Location> currentLocs) {
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
			mLogger.debug("###################### STACK UPDATE #########################");
			mergeList.forEach(loc -> mLogger.debug("*" + loc));
			mLogger.debug("##################### STACK UPDATE END #######################");
		}
		mComputationStackNWay.push(mergeList);
		return targets;
	}

	// function that returns all outgoing locations of a list of locations
	private List<Transition> getAllOutgoingTransitions(final List<Location> currentLocs) {
		final List<Transition> alloutgoing = new ArrayList<>();
		for (final Location loc : currentLocs) {
			alloutgoing.addAll(loc.getOutgoingTransitions());
		}
		return alloutgoing;
	}

	// function that tries to get a location if it exists, else it creates it.
	private Location getLocationNWay(final List<Location> mergeList) {
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

	// function that merges N locations and returns the merged one.
	private Location mergeLocationsNWay(final int incrementAndGet, final List<Location> mergeList) {
		String name = "loc_";
		String invariant = "";
		String flow = "";
		String forbiddenConstraint = "";
		boolean forbidden = false;
		mergeList.sort(Comparator.comparing(Location::getInvariant));
		// merge each locations invariant,flow and name
		for (final Location loc : mergeList) {
			name += loc.getName() + "_";
			invariant = intersectStrings(invariant, loc.getInvariant());
			flow = intersectStrings(flow, loc.getFlow());
			if (!forbiddenConstraint.contains(loc.getForbiddenConstraint())) {
				if (forbiddenConstraint.isEmpty() && !loc.getForbiddenConstraint().isEmpty()) {
					forbiddenConstraint += loc.getForbiddenConstraint();
				} else if (!loc.getForbiddenConstraint().isEmpty()) {
					forbiddenConstraint += "|" + loc.getForbiddenConstraint();
				}
			}

			if (loc.isForbidden()) {
				forbidden = true;
			}
		}
		// create locations
		final Location merged = new Location(incrementAndGet, name);
		merged.setInvariant(invariant);
		merged.setFlow(flow);
		merged.setForbiddenConstraint(forbiddenConstraint);
		merged.setForbidden(forbidden);
		return merged;
	}

	// function that merges parameters
	private void mergeParametersNWay(final Set<HybridAutomaton> automata) {
		// all parameters and constants are local after the parallel composition
		// is done.
		for (final HybridAutomaton aut : automata) {
			mLocalConstsMerge.addAll(aut.getGlobalConstants());
			mLocalConstsMerge.addAll(aut.getLocalConstants());
			mLocalParamsMerge.addAll(aut.getGlobalParameters());
			mLocalParamsMerge.addAll(aut.getLocalParameters());
			mLabelsMerge.addAll(aut.getLabels());
		}
		// define global labels.
		anaylseLabels(automata);
	}

	// function that determines which labels are globally used.
	private void anaylseLabels(final Set<HybridAutomaton> automata) {
		// just count how often the label appears.
		// if it appears in an automaton, increment a counter.
		// every label, which occurs more than 1 time in the automata, is a
		// global label.
		final Map<String, Integer> labelCount = new HashMap<>();
		for (final HybridAutomaton aut : automata) {
			final Set<String> labels = aut.getLabels();
			for (final String label : labels) {
				final int count = labelCount.containsKey(label) ? labelCount.get(label) : 0;
				labelCount.put(label, count + 1);
				if (labelCount.get(label) > 1) {
					mGlobalLabels.add(label);
				}
			}
		}
	}

	private void cleanUpMembers() {
		// clean up all members, necessary for multiple parallel compositions
		mGlobalConstsMerge = new HashSet<>();
		mGlobalParamsMerge = new HashSet<>();
		mLocalConstsMerge = new HashSet<>();
		mLocalParamsMerge = new HashSet<>();
		mLabelsMerge = new HashSet<>();
		mGlobalLabels = new HashSet<>();
		mLocationsMerge = new HashMap<>();
		mTransitionMerge = new ArrayList<>();
		mCreatedLocations = new HashMap<>();
		mIdCounter = new AtomicInteger(0);
		mVisitedLocations = new HashSet<>();
	}

	/**
	 * Function that creates a transition
	 *
	 * @param source
	 * @param target
	 * @param label
	 * @param guard
	 * @param update
	 * @return Hybrid Automata Transition
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
	 * Helper function to merge two strings into a string of the form
	 * "str1 && str2" Used for intersecting guards and updates of transitions in
	 * this class.
	 */
	private String intersectStrings(final String str1, final String str2) {
		String intersection;
		final String string1 = (str1 == null) ? "" : str1;
		final String string2 = (str2 == null) ? "" : str2;
		if (string1.equals(string2) || (!"".equals(string1) && "".equals(string2))) {
			intersection = string1;
		} else if (!"".equals(string1) && !"".equals(string2)) {
			intersection = string1 + " & " + string2;
		} else if ("".equals(string1) && !"".equals(string2)) {
			intersection = string2;
		} else {
			intersection = "";
		}
		return intersection;
	}
}
