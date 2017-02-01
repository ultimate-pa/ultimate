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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

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
	private Map<String, Integer> mCreatedLocations;
	private Stack<LocationPair> mComputationStack;
	private Set<String> mVisitedLocations;
	
	public ParallelCompositionGenerator(ILogger logger) {
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
		mComputationStack = new Stack<>();
		mVisitedLocations = new HashSet<>();
	}
	
	/**
	 * Function that computes the parallel composition of two hybrid automata
	 * 
	 * @param automaton1
	 * @param automaton2
	 * @param mergedLocationToPair
	 * @param binds
	 * @return
	 */
	public HybridAutomaton computeParallelComposition(HybridAutomaton automaton1, HybridAutomaton automaton2,
			Map<Location, LocationPair> mergedLocationToPair) {
		// name
		final String nameMerge = automaton1.getName() + "||" + automaton2.getName();
		// labels are merged with union
		mLabelsMerge.addAll(automaton1.getLabels());
		mLabelsMerge.addAll(automaton2.getLabels());
		splitLabels(automaton1.getName(), automaton2.getName(), automaton1.getLabels(), automaton2.getLabels());
		// merge variables
		mergeVariables(automaton1, automaton2);
		// locations
		final Map<Integer, Location> locations1 = automaton1.getLocations();
		final Map<Integer, Location> locations2 = automaton2.getLocations();
		// 1. get the initial locations, merge them
		// 2. get the outgoing transitions from the initials
		// 3. compare and merge the outgoing transitions
		// 4. Repeat
		final Location initial1 = automaton1.getInitialLocation();
		final Location initial2 = automaton2.getInitialLocation();
		final LocationPair locpair = new LocationPair(initial1, initial2);
		mInitialLocationMerge = getLocation(locpair.toString(), initial1, initial2);
		// add to map of the form merged loc -> locpair
		mergedLocationToPair.put(mInitialLocationMerge, locpair);
		// Add the initial locations to a Stack which holds LocationPair objects
		mComputationStack.push(new LocationPair(initial1, initial2));
		createLocationsAndTransitions(locations1, locations2, mergedLocationToPair);
		final HybridAutomaton hybAut = new HybridAutomaton(nameMerge, mLocationsMerge, mInitialLocationMerge,
				mTransitionMerge, mLocalParamsMerge, mLocalConstsMerge, mGlobalParamsMerge, mGlobalConstsMerge,
				mLabelsMerge, mLogger);
		// clean up
		cleanUpMembers();
		return hybAut;
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
		mComputationStack = new Stack<>();
		mVisitedLocations = new HashSet<>();
	}
	
	/**
	 * "Helper function" that Merges transitions and locations. 1. Pop from ComputationStack and get a location pair 2.
	 * Look up Outgoing transitions, calculate parallel products of locations/transitions 3. Add merged locations to
	 * ComputationStack in order to calculate 2. of their successors.
	 * 
	 * @param locations1
	 * @param locations2
	 * @param mergedLocationToPair
	 * @param automatonName1
	 * @param automatonName2
	 */
	private void createLocationsAndTransitions(Map<Integer, Location> locations1, Map<Integer, Location> locations2,
			Map<Location, LocationPair> mergedLocationToPair) {
		// TODO: reduce cyclomatic Complexity + make the whole function more understandable + add more seperate
		// functions
		while (!mComputationStack.isEmpty()) {
			final LocationPair locpair = mComputationStack.pop();
			if (mVisitedLocations.contains(locpair.toString())) {
				continue;
			}
			final Location currentLoc1 = locpair.getLocation1();
			final Location currentLoc2 = locpair.getLocation2();
			// get all outgoing transitions and set labels,guards,updates
			final List<Transition> outgoing1 = currentLoc1.getOutgoingTransitions();
			final List<Transition> outgoing2 = currentLoc2.getOutgoingTransitions();
			// if there are no outgoing transitions in either location, we can simply merge them and continue.
			if (outgoing1.isEmpty() && outgoing2.isEmpty()) {
				final Location source = getLocation(locpair.toString(), currentLoc1, currentLoc2);
				mLocationsMerge.put(source.getId(), source);
				mergedLocationToPair.put(source, locpair);
				continue;
			}
			// local vars for the loop
			Location srcLoc1;
			Location srcLoc2;
			Location tarLoc1;
			Location tarLoc2;
			String srcLocPair;
			String tarLocPair;
			String srcTarLocPair1;
			String srcTarLocPair2;
			Transition currentTransition1 = null;
			Transition currentTransition2 = null;
			String currentLabel1 = "";
			String currentGuard1 = "";
			String currentUpdate1 = "";
			String currentLabel2 = "";
			String currentGuard2 = "";
			String currentUpdate2 = "";
			while (outgoing1.listIterator().hasNext() || outgoing2.listIterator().hasNext()) {
				srcLoc1 = currentLoc1;
				srcLoc2 = currentLoc2;
				mVisitedLocations.add((new LocationPair(srcLoc1, srcLoc2)).toString());
				// if there is a transition, get it
				// if there is no transition, the target is the source.
				if (outgoing1.listIterator().hasNext()) {
					currentTransition1 = outgoing1.listIterator().next();
					tarLoc1 = locations1.get(currentTransition1.getTargetId());
					currentLabel1 = (currentTransition1.getLabel() != null) ? currentTransition1.getLabel() : "";
					currentGuard1 = (currentTransition1.getGuard() != null) ? currentTransition1.getGuard() : "";
					currentUpdate1 = (currentTransition1.getUpdate() != null) ? currentTransition1.getUpdate() : "";
				} else {
					tarLoc1 = srcLoc1;
				}
				if (outgoing2.listIterator().hasNext()) {
					currentTransition2 = outgoing2.listIterator().next();
					tarLoc2 = locations2.get(currentTransition2.getTargetId());
					currentLabel2 = (currentTransition2.getLabel() != null) ? currentTransition2.getLabel() : "";
					currentGuard2 = (currentTransition2.getGuard() != null) ? currentTransition2.getGuard() : "";
					currentUpdate2 = (currentTransition2.getUpdate() != null) ? currentTransition2.getUpdate() : "";
				} else {
					tarLoc2 = srcLoc2;
				}
				srcLocPair = srcLoc1 + "," + srcLoc2;
				tarLocPair = tarLoc1 + "," + tarLoc2;
				final boolean synchronization = isSynchronization(currentLabel1, currentLabel2);
				// if the labels are equal merge the transition and location right away
				if (synchronization) {
					// if the location exists, get it, else create a new one from the source locations
					final Location source = getLocation(srcLocPair, srcLoc1, srcLoc2);
					final Location target = getLocation(tarLocPair, tarLoc1, tarLoc2);
					// transition
					final Transition trans = createTransition(source, target, currentLabel1,
							intersectStrings(currentGuard1, currentGuard2),
							intersectStrings(currentUpdate1, currentUpdate2));
					mTransitionMerge.add(trans);
					// add incoming/outgoing transitions to locations
					source.addOutgoingTransition(trans);
					target.addIncomingTransition(trans);
					// add to locations
					mLocationsMerge.put(source.getId(), source);
					mLocationsMerge.put(target.getId(), target);
					outgoing1.remove(currentTransition1);
					outgoing2.remove(currentTransition2);
					final LocationPair locationPair = new LocationPair(tarLoc1, tarLoc2);
					mComputationStack.push(locationPair);
					mergedLocationToPair.put(target, locationPair);
				} else {
					// if one or both labels are local OR either one of them is empty, we can merge locations.
					// in order to do that, it is necessary to compute all possible combinations.
					// from s1,s2 -> s1,t2 AND t1,s2
					// pairs s1,t2 and t1,s2
					srcTarLocPair1 = srcLoc1 + "," + tarLoc2;
					srcTarLocPair2 = tarLoc1 + "," + srcLoc2;
					// if the location exists, get it, else create a new one from the source location pairs
					final Location source = getLocation(srcLocPair, srcLoc1, srcLoc2);
					// Create 2 target locations
					// if the locations exists, get it, else create a new one from the location pairs
					// s1,t2
					final Location target1 = getLocation(srcTarLocPair1, srcLoc1, tarLoc2);
					// t1,s2
					final Location target2 = getLocation(srcTarLocPair2, tarLoc1, srcLoc2);
					// Create 2 transitions
					// s1,s2 ---> s1,t2
					final Transition srcTar1 =
							createTransition(source, target1, currentLabel2, currentGuard2, currentUpdate2);
					// s1,s2 ---> t1,s2
					final Transition srcTar2 =
							createTransition(source, target2, currentLabel1, currentGuard1, currentUpdate1);
					// incoming /outgoing transitions
					if (source.getId() != target1.getId() && !mGlobalLabels.contains(srcTar1.getLabel())) {
						source.addOutgoingTransition(srcTar1);
						target1.addIncomingTransition(srcTar1);
						mTransitionMerge.add(srcTar1);
						final LocationPair srcTarPair = new LocationPair(srcLoc1, tarLoc2);
						mComputationStack.push(srcTarPair);
						mergedLocationToPair.put(target1, srcTarPair);
						
					}
					if (source.getId() != target2.getId() && !mGlobalLabels.contains(srcTar2.getLabel())) {
						source.addOutgoingTransition(srcTar2);
						target2.addIncomingTransition(srcTar2);
						mTransitionMerge.add(srcTar2);
						final LocationPair tarSrcPair = new LocationPair(tarLoc1, srcLoc2);
						mComputationStack.push(tarSrcPair);
						mergedLocationToPair.put(target2, tarSrcPair);
					}
					break;
				}
			}
		}
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
	private Transition createTransition(Location source, Location target, String label, String guard, String update) {
		final Transition trans = new Transition(source, target);
		trans.setLabel(label);
		trans.setGuard(guard);
		trans.setUpdate(update);
		return trans;
	}
	
	/**
	 * function that returns a location if it exsits, else it creates it
	 * 
	 * @param locPair
	 * @param loc1
	 * @param loc2
	 * @return
	 */
	private Location getLocation(String locPair, Location loc1, Location loc2) {
		Location loc;
		if (mCreatedLocations.containsKey(locPair)) {
			final int locId = mCreatedLocations.get(locPair);
			loc = mLocationsMerge.get(locId);
		} else {
			loc = mergeLocations(mIdCounter.incrementAndGet(), loc1, loc2);
			mCreatedLocations.put(locPair, mIdCounter.get());
			mLocationsMerge.put(loc.getId(), loc);
		}
		// hack TODO: change this
		if (loc == null) {
			loc = mergeLocations(mIdCounter.incrementAndGet(), loc1, loc2);
			mCreatedLocations.put(locPair, mIdCounter.get());
			mLocationsMerge.put(loc.getId(), loc);
		}
		return loc;
	}
	
	private void splitLabels(String automatonName1, String automatonName2, Set<String> labels1, Set<String> labels2) {
		final Set<String> locLabs1 = new HashSet<>();
		final Set<String> locLabs2 = new HashSet<>();
		labels1.forEach(lab1 -> {
			if (labels2.contains(lab1)) {
				mGlobalLabels.add(lab1);
			} else {
				locLabs1.add(lab1);
			}
		});
		mLocalLabels.put(automatonName1, locLabs1);
		labels2.forEach(lab1 -> {
			if (labels1.contains(lab1)) {
				mGlobalLabels.add(lab1);
			} else {
				locLabs2.add(lab1);
			}
		});
		mLocalLabels.put(automatonName2, locLabs2);
	}
	
	/*
	 * helper function to determine if 2 labels synchronize
	 */
	private boolean isSynchronization(String currentLabel1, String currentLabel2) {
		final boolean bothEmpty = ("".equals(currentLabel1) && "".equals(currentLabel2)) ? true : false;
		final boolean equalLabels = currentLabel1.equals(currentLabel2) ? true : false;
		final boolean bothGlobal = mGlobalLabels.contains(currentLabel1) && mGlobalLabels.contains(currentLabel2);
		return !bothEmpty && equalLabels && bothGlobal;
	}
	
	private void mergeVariables(HybridAutomaton automaton1, HybridAutomaton automaton2) {
		// All variables in a merged automata are LOCAL.
		// local params
		mLocalParamsMerge.addAll(automaton1.getLocalParameters());
		mLocalParamsMerge.addAll(automaton2.getLocalParameters());
		mLocalParamsMerge.addAll(automaton1.getGlobalParameters());
		mLocalParamsMerge.addAll(automaton2.getGlobalParameters());
		// local consts
		mLocalConstsMerge.addAll(automaton1.getLocalConstants());
		mLocalConstsMerge.addAll(automaton2.getLocalConstants());
		mLocalConstsMerge.addAll(automaton1.getGlobalConstants());
		mLocalConstsMerge.addAll(automaton2.getGlobalConstants());
	}
	
	/*
	 * helper function to merge locations
	 */
	private Location mergeLocations(int id, Location loc1, Location loc2) {
		final String locname = "loc_" + loc1.getId() + "_" + loc2.getId();
		final Location loc = new Location(id, locname);
		loc.setFlow(intersectStrings(loc1.getFlow(), loc2.getFlow()));
		loc.setInvariant(intersectStrings(loc1.getInvariant(), loc2.getInvariant()));
		return loc;
	}
	
	/*
	 * Helper function to merge two strings into a string of the form "str1 && str2" Used for intersecting guards and
	 * updates of transitions in this class.
	 */
	private String intersectStrings(String str1, String str2) {
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
