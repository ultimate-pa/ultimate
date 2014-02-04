/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Event;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class BranchingProcessToUltimateModel<S, C> {
	
	
	
	@SuppressWarnings("unchecked")
	public IElement getUltimateModelOfBranchingProcess(BranchingProcess<S, C> branchingProcess) {
		BranchingProcessInitialNode<S, C> graphroot = new BranchingProcessInitialNode<S, C>(branchingProcess);
		
		Collection<Condition<S, C>> initialStates = branchingProcess.initialConditions();
//		Collection<Event<S,C>> cutOffEvents = net.getCutOffEvents();
		
		Map<Condition<S, C>,ConditionNode<S,C>> place2ConditionNode =
			new HashMap<Condition<S, C>,ConditionNode<S,C>>();
		Map<Event<S, C>,EventNode<S,C>> transition2EventNode =
			new HashMap<Event<S, C>,EventNode<S,C>>();

		LinkedList<Object> queue = 
			new LinkedList<Object>(initialStates);
	
		// add all initial states to model - all are successors of the graphroot
		for (Condition<S, C> place : initialStates) {
			ConditionNode<S,C> ConditionNode = new ConditionNode<S,C>(place,branchingProcess);
			place2ConditionNode.put(place,ConditionNode);
			graphroot.connectOutgoing(ConditionNode);
			
		}
		
		while (!queue.isEmpty()) {
			Object node = queue.removeFirst();
			
			if (node instanceof Condition) {
				Condition<S,C> place = (Condition<S,C>) node;
				ConditionNode<S,C> ConditionNode = place2ConditionNode.get(place);
				for (Event<S,C> transition : place.getSuccessorEvents()) {
					EventNode<S,C> transNode = 
						transition2EventNode.get(transition);
					if (transNode == null) {
						transNode = new EventNode<S,C>(transition);
						transition2EventNode.put(transition, transNode);
						queue.add(transition);
					}
					ConditionNode.connectOutgoing(transNode);
				}
			}
			else if (node instanceof Event) {
				Event<S,C> transition = (Event<S,C>) node;
				EventNode<S,C> EventNode = 
					transition2EventNode.get(transition);
				for (Condition<S, C> place : transition.getSuccessorConditions()) {
					ConditionNode<S,C> ConditionNode = place2ConditionNode.get(place);
					if (ConditionNode == null) {
						
						ConditionNode = new ConditionNode<S,C>(place,branchingProcess);
						place2ConditionNode.put(place, ConditionNode);
						queue.add(place);
					}
					EventNode.connectOutgoing(ConditionNode);
				}
			}
		}
		return graphroot;
	}

}
