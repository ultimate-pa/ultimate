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
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;

/**
 * Generator that creates a parallel composition from {@link HybridAutomaton} instances.
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * 
 */
public class ParallelCompositionGenerator {
	
	private final ILogger mLogger;
	private final Set<String> mGlobalConstsMerge;
	private final Set<String> mGlobalParamsMerge;
	private final Set<String> mLocalConstsMerge;
	private final Set<String> mLocalParamsMerge;
	private final Set<String> mLabelsMerge;
	private final Set<String> mGlobalLabels;
	private final Map<String,Set<String>> mLocalLabels;
	private final Map<Integer, Location> mLocationsMerge;
	private final List<Transition> mTransitionMerge;
	private final Map<String,Integer> mCreatedLocations;
	private final AtomicInteger mIdCounter;
	
	public ParallelCompositionGenerator(ILogger logger){
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
	}
		
	/**
	 * Function that computes the parallel composition of two hybrid automata
	 * TODO: regard local and global parameters, regard automata without transitions if necessary, optimize
	 * @param automaton1
	 * @param automaton2
	 * @return 
	 */		
	public HybridAutomaton computeParallelComposition(HybridAutomaton automaton1,HybridAutomaton automaton2){
		// name
		final String nameMerge = automaton1.getName() + "||" + automaton2.getName();
		// labels are merged with union and splitted in local and global labels
		mLabelsMerge.addAll(automaton1.getLabels());
		mLabelsMerge.addAll(automaton2.getLabels());
		// for the parallel composition it is mandatory to split labels into local and global
		splitLabels(automaton1.getName(),automaton2.getName(),automaton1.getLabels(), automaton2.getLabels());
		// merge variables
		mergeVariables(automaton1,automaton2);
		// locations
		final Map<Integer, Location> locations1 = automaton1.getLocations();
		final Map<Integer, Location> locations2 = automaton2.getLocations();
		// 1. get the initial locations, merge them
		// 2. get the outgoing transitions from the initials
		// 3. compare and merge the outgoing transitions
		// 4. Repeat with target locations
		Location initial1 = locations1.get(1);
		Location initial2 = locations2.get(1);
		// Use an recursive function to create the merged transitions and locations
		// It start the call with both initial locations, create the merged locations and transitions
		// after that it will take the target locations of the created transitions and call the function again.
		createLocationsAndTransitions(initial1,initial2, locations1,locations2, automaton1.getName(),automaton2.getName());        
		HybridAutomaton hybAut = new HybridAutomaton(nameMerge, mLocationsMerge, mTransitionMerge,mLocalParamsMerge,
				                                     mLocalConstsMerge, mGlobalParamsMerge, mGlobalConstsMerge, mLabelsMerge, mLogger);
		mLogger.info(hybAut.toString());
		return hybAut;
	}
	
	// TODO: Fix complexity (use a priority queue instead of recursive calls) 
	// Add Termination condition!
	private void createLocationsAndTransitions(Location currentLoc1, Location currentLoc2, Map<Integer, Location> locations1,
												Map<Integer, Location> locations2, String aut1Name, String aut2Name) {
		// local vars for the loop
        Location srcLoc1;
        Location srcLoc2;
        Location tarLoc1;
        Location tarLoc2;
        String srcLocPair;
        String tarLocPair;
        String srcTarLocPair1;
        String srcTarLocPair2;
        // get all outgoing transitions and set labels,guards,updates
		List<Transition> outgoing1 = currentLoc1.getOutgoingTransitions();
		List<Transition> outgoing2 = currentLoc2.getOutgoingTransitions();
		Transition currentTransition1 = null;
		Transition currentTransition2 = null;
		String currentLabel1 = "";
		String currentGuard1 = "";
		String currentUpdate1 = "";
		String currentLabel2 = "";
		String currentGuard2 = "";
		String currentUpdate2 = "";
		while(outgoing1.iterator().hasNext() || outgoing2.iterator().hasNext()){
			srcLoc1 = currentLoc1;
			srcLoc2 = currentLoc2;
			// if there is a transition, get it
			// if there is no transition, the target is the source.
			if(outgoing1.iterator().hasNext()){
				currentTransition1 = outgoing1.iterator().next();
				tarLoc1 = locations1.get(currentTransition1.getTargetId());
				currentLabel1 = (currentTransition1.getLabel() != null) ? currentTransition1.getLabel() : "";
				currentGuard1 = (currentTransition1.getGuard() != null) ? currentTransition1.getGuard() : "";
				currentUpdate1 = (currentTransition1.getUpdate() != null) ? currentTransition1.getUpdate() : "";
			} else{
				tarLoc1 = srcLoc1;
			}
			if(outgoing2.iterator().hasNext()){
				currentTransition2 = outgoing2.iterator().next();
				tarLoc2 = locations2.get(currentTransition2.getTargetId());
				currentLabel2 = (currentTransition2.getLabel() != null) ? currentTransition2.getLabel() : "";
				currentGuard2 = (currentTransition2.getGuard() != null) ? currentTransition2.getGuard() : "";
				currentUpdate2 = (currentTransition2.getUpdate() != null) ? currentTransition2.getUpdate() : "";
			} else{
				tarLoc2 = srcLoc2;
			}
			srcLocPair = srcLoc1 + "," + srcLoc2;
			tarLocPair = tarLoc1 + "," + tarLoc2;
			boolean synchronization;
			if(currentLabel1 != null && currentLabel2 != null){
				if(currentLabel1.equals(currentLabel2)){
					synchronization = true;
				}else{
					synchronization = false;
				}
			} else {
				synchronization	= false;
			}
    		// if the labels are equal merge the transition and location right away
    		if(synchronization){
    			// if the location exists, get it, else create a new one from the source locations
    			Location source = getLocation(srcLocPair, srcLoc1, srcLoc2);
    			// if the location exists, get it, else create a new one from the target locations
    			Location target = getLocation(tarLocPair, tarLoc1, tarLoc2);     			
    			// transition
    			Transition trans = new Transition(source, target);
    			trans.setLabel(currentLabel1);
    			trans.setGuard(intersectStrings(currentGuard1, currentGuard2));
    			trans.setUpdate(intersectStrings(currentUpdate1, currentUpdate2));
    			mTransitionMerge.add(trans);
    			// add incoming/outgoing transitions to locations
    			source.addOutgoingTransition(trans);
    			target.addIncomingTransition(trans);
    			// add to locations
    			mLocationsMerge.put(source.getId(), source);
    			mLocationsMerge.put(target.getId(), target);
    			createLocationsAndTransitions(tarLoc1, tarLoc2, locations1, locations2, aut1Name, aut2Name);
    		} else if(isMergeValid(aut1Name,aut2Name, currentLabel1, currentLabel2)) {
    			// if one or both labels are local OR either one of them is empty, we can merge locations.
    			// in order to do that, it is necessary to compute all possible combinations.
    			// from s1,s2 -> s1,t2 AND t1,s2
    			// pairs s1,t2 and t1,s2
    			srcTarLocPair1 = srcLoc1 + "," + tarLoc2;
    			srcTarLocPair2 = tarLoc1 + "," + srcLoc2;
    			// if the location exists, get it, else create a new one from the source location pairs
    			Location source = getLocation(srcLocPair,srcLoc1,srcLoc2);
    			// Create 2 target locations		        		
    			// if the locations exists, get it, else create a new one from the location pairs
    			// s1,t2
    			Location target1 =  getLocation(srcTarLocPair1, srcLoc1, tarLoc2);
    			// t1,s2
    			Location target2 = getLocation(srcTarLocPair2, tarLoc1, srcLoc2);
    			// Create 2 transitions
    			// s1,s2 ---> s1,t2
    			Transition srcTar1 = new Transition(source, target1);
    			srcTar1.setGuard(currentGuard2);
    			srcTar1.setUpdate(currentUpdate2);
    			srcTar1.setLabel(currentLabel2);
    			// s1,s2 ---> t1,s2
    			Transition srcTar2 = new Transition(source, target2);
    			srcTar2.setGuard(currentGuard1);
    			srcTar2.setUpdate(currentUpdate1);
    			srcTar2.setLabel(currentLabel1);
    			// incoming /outgoing transitions
    			source.addOutgoingTransition(srcTar1);
    			source.addOutgoingTransition(srcTar2);
    			target1.addIncomingTransition(srcTar1);
    			target2.addIncomingTransition(srcTar2);
    			// recursive calls
    			createLocationsAndTransitions(srcLoc1, tarLoc2, locations1, locations2, aut1Name, aut2Name);
    			createLocationsAndTransitions(tarLoc1, srcLoc2, locations1, locations2, aut1Name, aut2Name);
    		} else {
    			continue;
    		}
		}		
	}

	private Location getLocation(String locPair, Location loc1, Location loc2) {
		Location loc;
		if(mCreatedLocations.containsKey(locPair)){
			int locId = mCreatedLocations.get(locPair);
			loc = mLocationsMerge.get(locId);
		} else{
			loc = mergeLocations(mIdCounter.incrementAndGet(), loc1, loc2);
			mCreatedLocations.put(locPair, mIdCounter.get());
		}
		return loc;
	}

	private void splitLabels(String automatonName1, String automatonName2, Set<String> labels1, Set<String> labels2) {
		Set<String> locLabs1 = new HashSet<>();
		Set<String> locLabs2 = new HashSet<>();
		labels1.forEach(lab1 -> {
			if(labels2.contains(lab1)){
				mGlobalLabels.add(lab1);
			} else{
				locLabs1.add(lab1);
			}
		});
		mLocalLabels.put(automatonName1, locLabs1);
		labels2.forEach(lab1 -> {
			if(labels1.contains(lab1)){
				mGlobalLabels.add(lab1);
			} else{
				locLabs2.add(lab1);
			}
		});
		mLocalLabels.put(automatonName2, locLabs2);
	}

	private boolean isMergeValid(String automatonname1, String automatonname2, String label1, String label2) {
		boolean isLocal1 = mLocalLabels.get(automatonname1).contains(label1);
		boolean isLocal2 = mLocalLabels.get(automatonname2).contains(label2);
		// double check if labels are not global
		if(mGlobalLabels.contains(label1) || mGlobalLabels.contains(label2)){
			return false;
		}
		boolean isEmpty1 = (label1 == null || "".equals(label1)) ? true : false;
		boolean isEmpty2 = (label2 == null || "".equals(label2)) ? true : false;
		if((isLocal1 && isLocal2) || (isLocal1 && isEmpty2) || (isLocal2 && isEmpty1) || (isEmpty1 && isEmpty2)){
			return true;
		}else{
			return false;
		}
	}
	
	private void mergeVariables(HybridAutomaton automaton1, HybridAutomaton automaton2) {
		// global consts
		mGlobalConstsMerge.addAll(automaton1.getGlobalConstants());
		mGlobalConstsMerge.addAll(automaton2.getGlobalConstants());
		// global params
		mGlobalParamsMerge.addAll(automaton1.getGlobalParameters());
		mGlobalParamsMerge.addAll(automaton2.getGlobalParameters());
		// local consts
		mLocalConstsMerge.addAll(automaton1.getLocalConstants());
		mLocalConstsMerge.addAll(automaton2.getLocalConstants());
		// local params
		mLocalParamsMerge.addAll(automaton1.getLocalParameters());
		mLocalParamsMerge.addAll(automaton2.getLocalParameters());		
	}

	/* 
	 * helper function to create a transition which holds the same label,guard,update as a given parent Transition	
	 */
	private Transition createTransitionFromParent(Location source, Location target, Transition parent){
		Transition trans = new Transition(source, target);
		trans.setLabel(parent.getLabel());
		trans.setGuard(parent.getGuard());
		trans.setUpdate(parent.getUpdate());
		return trans;
	}
	
	/*
	 * helper function to merge locations
	 */
	private Location mergeLocations(int id, Location loc1, Location loc2){
		Location loc = new Location(id);
		loc.setFlow(loc1.getFlow() + " && " + loc2.getFlow());
		loc.setInvariant(loc1.getInvariant() + " && " + loc2.getInvariant());
		return loc;
	}
	
	/*
	 * Helper function to merge two strings into a string of the form "str1 && str2"
	 * Used for intersecting guards and updates of transitions in this class.
	 */
	private String intersectStrings(String str1, String str2){
		String intersection;
		String string1 = (str1 == null) ? "" : str1;
		String string2 = (str2 == null) ? "" : str2;
		if(string1.equals(string2) || (!"".equals(string1) && "".equals(string2))){
			intersection = string1;
		} else if(!"".equals(string1) && !"".equals(string2)){
			intersection = string1 + " && " + string2;
		} else if("".equals(string1) && !"".equals(string2)){
			intersection = string2;
		}else{
			intersection = "";
		}
		return intersection;
	}
}
