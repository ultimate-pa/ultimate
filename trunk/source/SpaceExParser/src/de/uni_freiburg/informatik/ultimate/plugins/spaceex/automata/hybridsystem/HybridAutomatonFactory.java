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

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;

/**
 * Factory that creates {@link HybridAutomaton} instances.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * 
 */
public class HybridAutomatonFactory {
	
	private final ILogger mLogger;
	
	public HybridAutomatonFactory(ILogger logger){
		mLogger = logger;
	}
	
	public HybridAutomaton createHybridAutomatonFromComponent(final ComponentType automaton) {
		return new HybridAutomaton(automaton, mLogger);
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
		// variables are merged with union		
		final Set<String> gConstsMerge = new HashSet<>(automaton1.getGlobalConstants());
		final Set<String> gParamsMerge = new HashSet<>(automaton1.getGlobalParameters());
		final Set<String> lConstsMerge = new HashSet<>(automaton1.getLocalConstants());
		final Set<String> lParamsMerge = new HashSet<>(automaton1.getLocalParameters());
		gConstsMerge.addAll(automaton2.getGlobalConstants());
		gParamsMerge.addAll(automaton2.getGlobalParameters());
		lConstsMerge.addAll(automaton2.getLocalConstants());
		lParamsMerge.addAll(automaton2.getLocalParameters());
		// labels are merged with union
		final Set<String> labelsMerge = new HashSet<>(automaton1.getLabels());
		labelsMerge.addAll(automaton2.getLabels());		
		// locations
		final Map<Integer, Location> locations1 = automaton1.getLocations();
		final Map<Integer, Location> locations2 = automaton2.getLocations();
		final Map<Integer, Location> locationsMerge = new HashMap<>();
		// transitions
		final List<Transition> transitions1 = automaton1.getTransitions();
		final List<Transition> transitions2 = automaton2.getTransitions();
		final List<Transition> transitionMerge = new ArrayList<>();
		// Use AtomicInteger as counter for the ID.
        final AtomicInteger id = new AtomicInteger();
        // for the moment parallel composition only works if both automata have transitions
        if(transitions1.isEmpty() || transitions2.isEmpty()){
        	throw new UnsupportedOperationException("Only hybrid automata with transitions are supported,"
        											+ " one or both got no transitions");
        }
        // compare all transitions and merge them.
        for(Transition trans1 : transitions1){
        	for(Transition trans2 : transitions2){
        		Location srcLoc1 = locations1.get(trans1.getSourceId());
    			Location srcLoc2 = locations2.get(trans2.getSourceId());
    			Location tarLoc1 = locations1.get(trans1.getTargetId());
    			Location tarLoc2 = locations2.get(trans2.getTargetId());
        		// if the labels are equal they synchronize, merge them right away.
        		// also merge the locations right away.
        		if(trans1.getLabel().equals(trans2.getLabel())){
        			// source location
        			Location source = mergeLocations(id.incrementAndGet(), srcLoc1, srcLoc2);
        			// target location
        			Location target = mergeLocations(id.incrementAndGet(), tarLoc1, tarLoc2);
        			// transition
        			Transition trans = new Transition(source, target);
        			trans.setLabel(trans1.getLabel());
        			trans.setGuard(intersectStrings(trans1.getGuard(), trans2.getGuard()));
        			trans.setUpdate(intersectStrings(trans1.getUpdate(), trans2.getUpdate()));
        			transitionMerge.add(trans);
        			// add incoming/outgoing transitions to locations
        			source.addOutgoingTransition(trans);
        			target.addIncomingTransition(trans);
        			// add to locations
        			locationsMerge.put(source.getId(), source);
        			locationsMerge.put(target.getId(), target);
        		} else{
        			/* if the labels are not equal, it means they do not synchronize,
        			 * thus it is necessary to cover 4 cases:
        			 * - we are in both source locations s1,s2
        			 * - we are in both target locations t1,t2
        			 * - one in source s1, one in target t2
        			 * - one in target t1, one in source s2
        			*/ 
        			Location root = mergeLocations(id.incrementAndGet(), srcLoc1, srcLoc2);        			
        			Location branch1 = mergeLocations(id.incrementAndGet(), tarLoc1, srcLoc2);        			
        			Location branch2 = mergeLocations(id.incrementAndGet(), srcLoc1, tarLoc2);
        			Location end = mergeLocations(id.incrementAndGet(), tarLoc1, tarLoc2);	
        			// Transitions
        			Transition rootBranch1 = createTransitionFromParent(root, branch1, trans1);
        			Transition rootBranch2 = createTransitionFromParent(root, branch2, trans2);
        			Transition branch1End = createTransitionFromParent(branch1, end, trans2);
        			Transition branch2End = createTransitionFromParent(branch2, end, trans1);
        			// add incoming/outgoing transitions
        			root.addOutgoingTransition(rootBranch1);
        			root.addOutgoingTransition(rootBranch2);
        			branch1.addIncomingTransition(rootBranch1);
        			branch1.addOutgoingTransition(branch1End);
        			branch2.addIncomingTransition(rootBranch2);
        			branch2.addOutgoingTransition(branch2End);
        			end.addIncomingTransition(branch1End);
        			end.addIncomingTransition(branch2End);
        			// add to locations/transitions
        			locationsMerge.put(root.getId(),root);
        			locationsMerge.put(branch1.getId(), branch1);
        			locationsMerge.put(branch2.getId(), branch2);
        			locationsMerge.put(end.getId(), end);        			
        			transitionMerge.add(rootBranch1);
        			transitionMerge.add(rootBranch2);
        			transitionMerge.add(branch1End);
        			transitionMerge.add(branch2End);
        		}
        	}
        }
		HybridAutomaton hybAut = new HybridAutomaton(nameMerge, locationsMerge, transitionMerge,lParamsMerge,
				                                     lConstsMerge, gParamsMerge, gConstsMerge, labelsMerge, mLogger);
		mLogger.info(hybAut.toString());
		return hybAut;
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
